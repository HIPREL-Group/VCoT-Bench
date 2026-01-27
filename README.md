# VCoT-Bench: Evaluating via Verification Chain of Thought

**Table of Contents**:

- [Overview](#overview)

- [VCoT-Lift Setup](#vcot-lift-setup)

## Overview

**VCoT-Bench** is a benchmark designed to evaluate the formal verification capabilities of Large Language Models (LLMs). It is constructed using **VCoT-Lift**, which exposes internal verification reasoning by lifting low-level Z3 proofs into Verus-level verification steps.

### VCoT-Bench

- 📊 Multi-dimension Evaluation: Evaluates formal verification capability along three dimensions: *Ratio*, *Type*, and *Location*.

- 📈 **Ratio**: Evaluates an LLM’s ability to recover missing verification steps under varying degrees of information loss.

- 🌟 **Type**: Evaluates an LLM’s ability to reconstruct specific proof types.

- 📍 **Location**: Evaluates how the position of missing reasoning affects a model’s ability to recover the underlying logic.

### VCoT-Lift

**VCoT-Lift** is a multi-stage framework to lift the low-level logical reasoning embedded in Z3 proofs into comprehensive Verus-level verification steps. 

## VCoT-Lift Setup

Code for VCoT-Lift is included in "vcot-lift" folder. 

**Dependencies**: VCoT-Lift depends on Verus, visit Verus repository for more installation information: [https://github.com/verus-lang/verus](https://github.com/verus-lang/verus).

**Model Selection**: VCoT-Lift supports flexible model selection and currently integrates 16 models:

- **OpenAI**: GPT-5.2, GPT-5, GPT-5 mini, GPT-4o mini, GPT-4.1, o3
- **Anthropic**: Claude Sonnet 4.5, Claude Haiku 4.5, Claude Sonnet 4, Claude Opus 4.1
- **Google**: Gemini 3, Gemini 3 Flash, Gemini 2.5 pro, Gemini 2.5 Flash
- **DeepSeek**: DeepSeek V3.2, DeepSeek R1

You can configure the models used at different stages. By default, Gemini 3 is used for Proof Repair, and GPT-5.2 is used for all other stages.

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

Set up `verus_path` and `result_dir` in `config.json` under "vcot-lift" folder.

- `verus_path`: Path to your Verus executable file.
- `result_dir`: Path to the result directory where you want to store your results.

### Usage

```
cd vcot-lift
python main.py --file <verified.rs> --id <id>
```

**Key Parameters:**

- `--file`: A Verus-verified Rust program file start proof lifting.
- `--id` (optional): Result directory id for the lifting process. Default: time slot id.

**Example:** 

```
python main.py --file examples/task_id_240.rs --id task_id_240
```

**Output:**

All intermidiate outputs and final result will be store under `<result_path>/<id>`. The final transformed Verus program with verification steps will be shown in `verus_vs.rs`.
