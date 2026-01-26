# Instruction

You are an expert in Verus and Z3 SMT solver. You will be provided with a Verus program and a piece of Z3 proof. 

The Z3 proof provided is a collection of proof rule `lemma` and the corresponding proof context.
The `lemma` rule is a logical bridge that imports a fact proven manually in Verus into the SMT solver's context. Usuall it can be transformed into **a lemma function, a proof block, or a sequence of assertions.**

## Task

Your task is to analyze the Z3 proof and **examine** whether the proofs in the provided Verus program fully cover the internal reasoning steps shown in the Z3 proof. 

### Abstraction Barrier

You must NOT transform Z3 proof steps that are **Trivial** or **Redundant**. If the Z3 proof contains no reasoning beyond these categories, the Verus program must be considered complete. A Z3 proof step must be ignored if it falls into the following categories:

1. Trivial Reasoning

A *local reasoning* step is considered trivial. A reasoning step is deemed *local* if the Z3 solver can justify it using only the immediate facts available in its current context, without searching for additional axioms or unfolding complex definitions such as reflexivity and commutativity.

2. Redundant Reasoning

- Normalization: Purely structural changes, such as reordering terms or rewriting $a + b$ to $b + a$.

- Existing Properties: Any fact already established by current requires clauses, or existing proofs in the Verus code.

- Definition Expansion: Simple unfolding of spec functions that the solver can already see.

# Input Field 

## Verus program

```rust
{{verus_program}}
```

## Z3 Proof

```smt2
{{z3_proof}}
```

# Output Field

- If the current Verus program already contains all internal reasoning steps reflected in the Z3 proof, you should:
    1. Output the verdict `The proof is complete.` 
    2. Output **exactly** one code snippet enclosed in **```rust** that contains the corresponding Verus code implementing the reasoning steps from the Z3 proof.
    3. Output your analysis explaining how you get this mapping.

- If there are missing Verus proofs, you should: 
    1. Output the verdict `The proof is incomplete.` 
    2. Output your analysis explaining which reasoning steps are missing and why the proof is incomplete. **Do not include any code enclosed in ```rust in this analysis.**

**CRITICAL REQUIREMENTS:**

- Do not introduce `assume()` or `admit()` statements under any circumstances.

- Do not add comments in the program.