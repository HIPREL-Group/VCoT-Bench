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
model_gpt = LLM.create("model_gpt_5_2", logger)
model_gemini = LLM.create("gemini_3", logger)

logger.level("DEBUG")


def init_config(config_file: str = "./config.json"):
    global global_config 
    global_config = json.load(open(config_file, "r")) 


def build_dir(id):
    result_dir = global_config.get("result_dir")
    path = os.path.join(result_dir, id)
    if not os.path.exists(path):
        os.makedirs(path) 
    else:
        raise RuntimeError("folder already exist")


def proof_trans_check(verus_vs_path, result_path, num_proof, max_iter=5):
    transformer = Transformer(verus_vs_path=verus_vs_path,
                              max_iter=max_iter, 
                              model=model_gpt, 
                              logger=logger)
    for i in range(num_proof):
        result_trans_path = Path(result_path) / f"proof_trans{i}"
        logger.info(f"start transformer-checker loop for proof {i}")

        # Get Z3 proof
        z3_proof = Path(f".verus-log/z3_proof{i}.smt2").read_text()
        z3_proof = z3_proof.replace("unsat\n", "")

        transformer.execute(result_path=result_trans_path, z3_proof=z3_proof)
        logger.info(f"finish transformer-checker loop for proof {i}")


def proof_prune(verus_vs_path, result_path, max_iter=1):
    pruner = Pruner(verus_vs_path=verus_vs_path, 
                    max_iter=max_iter, 
                    model=model_gpt, 
                    logger=logger)
    pruner.execute(result_path=result_path)
        

def proof_repair(verus_vs_path, result_path, max_iter=10):
    repair = Repair(verus_vs_path=verus_vs_path,
                    max_iter=max_iter,
                    model=model_gemini,
                    logger=logger)
    return repair.execute(result_path=result_path)


def execute(verified_path, id=None):
    if id is None:
        id = id_maker()

    # initialize config and build dir
    init_config()
    build_dir(id)
    result_dir = global_config.get("result_dir")
    result_path = os.path.join(result_dir, id)

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
    proof_trans_check(verus_vs_path, result_path, num_proof, max_iter=5)

    # proof pruning
    ret = proof_prune(verus_vs_path, result_path, max_iter=1)

    # proof repair
    ret = proof_repair(verus_vs_path, result_path, max_iter=10)

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

    args = parser.parse_args()

    execute(args.file, args.id)


if __name__ == "__main__":
    main()
    