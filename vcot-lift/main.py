from loguru import logger
from util import id_maker, gain_proof
import os
import json
import argparse
from pathlib import Path
from llm import LLM
from proof_transformer import Transformer
from proof_pruner import Pruner
from proof_repair import Repair


global_config = dict()  # store information from config.json

# Pipeline stage -> (command-line flag, description, default model).
# A model is "<provider>:<model id>" or a shortcut name from MODEL_ALIASES in
# llm.py. The model of each stage is resolved with the precedence:
#   command-line flag > "models" section of config.json > default below
STAGES = {
    "proof_trans": ("--trans-model", "proof transformation", "model_gpt_5_2"),
    "proof_check": ("--check-model", "proof checking", "model_gpt_5_2"),
    "proof_prune": ("--prune-model", "proof pruning", "model_gpt_5_2"),
    "proof_repair": ("--repair-model", "proof repair", "gemini_3"),
}

logger.level("DEBUG")


def init_config(config_file: str = "./config.json"):
    global global_config
    global_config = json.load(open(config_file, "r"))


def resolve_stage_models(overrides=None):
    """Return {stage: "<provider>:<model id>"}, merging defaults, config.json and overrides."""
    configured = global_config.get("models", {})
    unknown_stages = set(configured) - set(STAGES)
    if unknown_stages:
        raise ValueError(
            f"Unknown stage(s) in config.json \"models\": {', '.join(sorted(unknown_stages))}. "
            f"Valid stages: {', '.join(STAGES)}"
        )

    stage_models = {stage: default for stage, (_, _, default) in STAGES.items()}
    stage_models.update(configured)
    stage_models.update({k: v for k, v in (overrides or {}).items() if v is not None})

    resolved = {}
    for stage, spec in stage_models.items():
        try:
            provider, model = LLM.parse(spec)
        except ValueError as e:
            raise ValueError(f"Invalid model for stage \"{stage}\": {e}") from None
        resolved[stage] = f"{provider}:{model}"
    return resolved


def model_spec(value):
    """argparse type: accept a valid model spec, report a usage error otherwise."""
    try:
        LLM.parse(value)
    except ValueError as e:
        raise argparse.ArgumentTypeError(str(e))
    return value


def create_models(stage_models):
    """Create one LLM client per distinct model and share it across stages."""
    clients = {name: LLM.create(name, logger) for name in set(stage_models.values())}
    return {stage: clients[name] for stage, name in stage_models.items()}


def build_dir(id):
    result_dir = global_config.get("result_dir")
    path = os.path.join(result_dir, id)
    if not os.path.exists(path):
        os.makedirs(path)
    else:
        raise RuntimeError("folder already exist")


def proof_trans_check(verus_vs_path, result_path, num_proof, trans_model, check_model, max_iter=5):
    transformer = Transformer(verus_vs_path=verus_vs_path,
                              max_iter=max_iter,
                              model=trans_model,
                              check_model=check_model,
                              logger=logger)
    for i in range(num_proof):
        result_trans_path = Path(result_path) / f"proof_trans{i}"
        logger.info(f"start transformer-checker loop for proof {i}")

        # Get Z3 proof
        z3_proof = Path(f".verus-log/z3_proof{i}.smt2").read_text()
        z3_proof = z3_proof.replace("unsat\n", "")

        transformer.execute(result_path=result_trans_path, z3_proof=z3_proof)
        logger.info(f"finish transformer-checker loop for proof {i}")


def proof_prune(verus_vs_path, result_path, model, max_iter=1):
    pruner = Pruner(verus_vs_path=verus_vs_path,
                    max_iter=max_iter,
                    model=model,
                    logger=logger)
    pruner.execute(result_path=result_path)


def proof_repair(verus_vs_path, result_path, model, max_iter=10):
    repair = Repair(verus_vs_path=verus_vs_path,
                    max_iter=max_iter,
                    model=model,
                    logger=logger)
    return repair.execute(result_path=result_path)


def execute(verified_path, id=None, model_overrides=None):
    if id is None:
        id = id_maker()

    # initialize config and models, then build dir
    init_config()
    stage_models = resolve_stage_models(model_overrides)
    for stage, name in stage_models.items():
        logger.info(f"model for {stage}: {name}")
    models = create_models(stage_models)

    build_dir(id)
    result_dir = global_config.get("result_dir")
    result_path = os.path.join(result_dir, id)
    Path(result_path, "models.json").write_text(json.dumps(stage_models, indent=4))

    verus_ph = Path(verified_path).read_text()
    verus_ph_path = os.path.join(result_path, "verus_ph.rs")
    verus_vs_path = os.path.join(result_path, "verus_vs.rs")
    Path(verus_ph_path).write_text(verus_ph)
    Path(verus_vs_path).write_text(verus_ph)

    # gain proof
    ret, num_proof = gain_proof(verus_ph_path)
    if not ret:
        logger.error("original Verus program cannot be verified!")
        raise RuntimeError("original Verus program cannot be verified!")

    # transfomer-checker loop
    proof_trans_check(verus_vs_path, result_path, num_proof,
                      trans_model=models["proof_trans"],
                      check_model=models["proof_check"],
                      max_iter=5)

    # proof pruning
    ret = proof_prune(verus_vs_path, result_path, model=models["proof_prune"], max_iter=1)

    # proof repair
    ret = proof_repair(verus_vs_path, result_path, model=models["proof_repair"], max_iter=10)

    verification_result_path = Path(result_path) / "verification_result.md"
    if ret:
        logger.info("verification succeed!")
        verification_result_path.write_text("verification succeed!")
    else:
        logger.info("verification failed.")
        verification_result_path.write_text("verification failed.")


def main():
    parser = argparse.ArgumentParser(
        description=': tranform the Z3 proof to Verus-level verfication steps'
    )

    parser.add_argument(
        '--file',
        type=str,
        required=True,
        help='Path to Verus-verified file'
    )

    parser.add_argument(
        '--id',
        type=str,
        default=None,
        help='Result directory id for the transformation (default: timestamp)'
    )

    model_group = parser.add_argument_group(
        'model selection',
        'Override the model of a stage for this run. Takes precedence over the '
        '"models" section of config.json. MODEL is "<provider>:<model id>" '
        f'with provider one of {", ".join(LLM.providers())} '
        '(e.g. anthropic:claude-opus-5-5), or a shortcut name from '
        'MODEL_ALIASES in llm.py (e.g. model_gpt_5_2, gemini_3).'
    )
    for stage, (flag, description, default) in STAGES.items():
        model_group.add_argument(
            flag,
            dest=stage,
            metavar='MODEL',
            type=model_spec,
            default=None,
            help=f'Model for {description} (built-in default: {default})'
        )

    args = parser.parse_args()

    model_overrides = {stage: getattr(args, stage) for stage in STAGES}
    execute(args.file, args.id, model_overrides)


if __name__ == "__main__":
    main()

