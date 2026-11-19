# VCoT-Bench: Evaluating via Verification Chain of Thought

**Accepted at ICML 2026**

📄 Paper: [Can LLMs Reason Like Automated Theorem Provers for Rust Verification? VCoT-Bench: Evaluating via Verification Chain of Thought](https://arxiv.org/abs/2603.18334) 

## Overview

**VCoT-Bench** is a benchmark designed to evaluate the formal verification capabilities of Large Language Models (LLMs). It is constructed using **VCoT-Lift**, which exposes internal verification reasoning by lifting low-level Z3 proofs into Verus-level verification steps.

### VCoT-Bench

- 📊 Multi-dimension Evaluation: Evaluates formal verification capability along three dimensions: *Ratio*, *Type*, and *Location*.

- 📈 **Ratio**: Evaluates an LLM’s ability to recover missing verification steps under varying degrees of information loss.

- 🌟 **Type**: Evaluates an LLM’s ability to reconstruct specific proof types.

- 📍 **Location**: Evaluates how the position of missing reasoning affects a model’s ability to recover the underlying logic.

### VCoT-Lift

**VCoT-Lift** is an LLM-based framework to lift the low-level Z3 proofs into explicit, human-readable Verus verification steps.

## VCoT-Lift Setup

Code for VCoT-Lift is included in "vcot-lift" folder. 

**Dependencies**: VCoT-Lift depends on Verus, visit Verus repository for more installation information: [https://github.com/verus-lang/verus](https://github.com/verus-lang/verus).

**Model Selection**: VCoT-Lift works with any model from OpenAI, Anthropic, Google Gemini, and DeepSeek. A model is written as `<provider>:<model id>`, where `<model id>` is the model name used by the provider's API, so switching to a newly released model only requires changing the model id:

| Provider  | `<provider>` | API key environment variable | Example |
|-----------|--------------|------------------------------|---------|
| OpenAI    | `openai`     | `OPENAI_API_KEY`    | `openai:gpt-5.2-2025-12-11` |
| Anthropic | `anthropic`  | `ANTHROPIC_API_KEY` | `anthropic:claude-opus-5-5` |
| Google    | `gemini`     | `GEMINI_API_KEY`    | `gemini:gemini-3-pro-preview` |
| DeepSeek  | `deepseek`   | `DEEPSEEK_API_KEY`  | `deepseek:deepseek-reasoner` |

The 16 models evaluated in the paper can also be selected by a shortcut name (defined in `MODEL_ALIASES` in `vcot-lift/llm.py`):

| Shortcut name | Model |
|---------------|-------|
| `model_gpt_5_2` | `openai:gpt-5.2-2025-12-11` |
| `model_gpt_5` | `openai:gpt-5-2025-08-07` |
| `model_gpt_5_mini` | `openai:gpt-5-mini-2025-08-07` |
| `model_gpt_4o_mini` | `openai:o4-mini-2025-04-16` |
| `model_gpt_4_1` | `openai:gpt-4.1-2025-04-14` |
| `model_gpt_o3` | `openai:o3-2025-04-16` |
| `claude_sonnet_4_5` | `anthropic:claude-sonnet-4-5-20250929` |
| `claude_haiku_4_5` | `anthropic:claude-haiku-4-5-20251001` |
| `claude_sonnet_4` | `anthropic:claude-sonnet-4-20250514` |
| `claude_opus_4_1` | `anthropic:claude-opus-4-1-20250805` |
| `gemini_3` | `gemini:gemini-3-pro-preview` |
| `gemini_3_flash` | `gemini:gemini-3-flash-preview` |
| `gemini-2.5-pro` | `gemini:gemini-2.5-pro` |
| `gemini-2.5-flash` | `gemini:gemini-2.5-flash` |
| `deepseek_v3_2` | `deepseek:deepseek-chat` |
| `deepseek_r1` | `deepseek:deepseek-reasoner` |

You can configure the model used at each stage of the pipeline (see [Configuration](#configuration)). By default, Gemini 3 is used for proof repair, and GPT-5.2 is used for all other stages.

### Installation

```
# 1. Clone repository

# 2. Install Python dependencies  
pip install -r requirements.txt

# 3. Set up API keys based on your model selection
export OPENAI_API_KEY=<your-openai-api-key> # default
export GEMINI_API_KEY=<your-gemini-api-key> # default
export ANTHROPIC_API_KEY=<your-anthropic-api-key>
export DEEPSEEK_API_KEY=<your-deepseek-api-key>
```

### Configuration

Set up `config.json` under "vcot-lift" folder:

```json
{
    "verus_path": "<path to verus executable file>",
    "result_dir": "<path to the result directory>",
    "models": {
        "proof_trans": "openai:gpt-5.2-2025-12-11",
        "proof_check": "openai:gpt-5.2-2025-12-11",
        "proof_prune": "openai:gpt-5.2-2025-12-11",
        "proof_repair": "gemini:gemini-3-pro-preview"
    }
}
```

- `verus_path`: Path to your Verus executable file.
- `result_dir`: Path to the result directory where you want to store your results.
- `models` (optional): Model used at each stage, as `<provider>:<model id>` or a shortcut name. Any stage left out uses its default.
  - `proof_trans`: Proof transformation, which lifts the Z3 proof into Verus verification steps.
  - `proof_check`: Proof checking, which checks the transformed proof against each Z3 proof rule.
  - `proof_prune`: Proof pruning, which removes trivial or redundant verification steps.
  - `proof_repair`: Proof repair, which fixes the program until Verus verifies it.

Only the API keys for the providers you select are required.

### Usage

```
cd vcot-lift
python main.py --file <verified.rs> --id <id>
```

**Key Parameters:**

- `--file`: A Verus-verified Rust program file start proof lifting.
- `--id` (optional): Result directory id for the lifting process. Default: time slot id.
- `--trans-model`, `--check-model`, `--prune-model`, `--repair-model` (optional): Model (`<provider>:<model id>` or a shortcut name) for the proof transformation, proof checking, proof pruning, and proof repair stage, respectively. These override the `models` section of `config.json` for a single run.

**Example:** 

```
python main.py --file examples/task_id_240.rs --id task_id_240

# use Claude Opus 5.5 for proof repair in this run
python main.py --file examples/task_id_240.rs --id task_id_240_claude --repair-model anthropic:claude-opus-5-5
```

**Output:**

All intermidiate outputs and final result will be store under `<result_path>/<id>`. The final transformed Verus program with verification steps will be shown in `verus_vs.rs`. The models used for each stage are recorded in `models.json`.

## Citation

If you find this work useful, please cite:

```bibtex
@article{xie2026can,
  title={Can LLMs Reason Like Automated Theorem Provers for Rust Verification? VCoT-Bench: Evaluating via Verification Chain of Thought},
  author={Xie, Zichen and Wang, Wenxi},
  journal={arXiv preprint arXiv:2603.18334},
  year={2026}
}
```

## License

This project is licensed under the [MIT License](LICENSE).
