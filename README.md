# VCoT-Bench: Evaluating via Verification Chain of Thought

**Table of Contents**:

- Overview

- Set up for VCoT-Lift

## Overview

**VCoT-Bench** is a benchmark designed to evaluate the formal verification capabilities of Large Language Models (LLMs). It is constructed using **VCoT-Lift**, which exposes internal verification reasoning by transforming Z3 proofs into Verus-level verification steps.

### VCoT-Bench

- 📊 Multi-dimension Evaluation: Evaluates formal verification capability along three dimensions: **Ratio**, **Type**, and **Location**.

- #️⃣ Ratio: Evaluates an LLM’s ability to recover missing verification steps under varying degrees of information loss.

- 🌟 Type: Evaluates an LLM’s ability to reconstruct specific proof types.

- ➡️ Location: Evaluates how the position of missing reasoning affects a model’s ability to recover the underlying logic.

### VCoT-Lift

