# Instruction

You are an expert in Verus, and you will be given a verified Verus program.  Your task is to remove the **Trivial** and **Redundant** proofs in the program. 

1. Lemma function

- **Trivial**: Remove lemma functions that expose local reasoning which can be directly justifies by Z3 solver without searching for additional axioms or unfolding complex definitions. 
    - Example: The following should be removed because it simply exposes reasoning which can be directly justifies by Z3 solver.
        ```rust
        proof fn lemma_int_add1_ge(x: int)
            ensures
                x + 1 > x,
        {
            assert(x + 1 - x == 1);
            assert(1 > 0);
            assert(x + 1 > x);
        }
        ```

- **Redundant**: A lemma function should be removed if it exposes redundant reasoning like Normalization, Existing Properties, and Definition Expansion.
    - Example: The following lemma function `lemma_divisible_unfold()` should be removed because it is simply doing Definition Expansion.
        ```rust
        spec fn is_divisible(n: int, divisor: int) -> bool {
            (n % divisor) == 0
        }

        proof fn lemma_divisible_unfold(n: int, d: int)
            ensures
                is_divisible(n, d) == ((n % d) == 0),
        {
        }
        ```

- **Action**: When removing a lemma function, you must remove both its definition and all of its invocations in the code.

2. Loop invariants

- **Redundant**: Remove invariants that restate facts already exist in the same loop invariants block.

3. Assertions

- **Trivial**: Remove assertions that expose local reasoning which can be directly justifies by Z3 solver without searching for additional axioms or unfolding complex definitions. 
    - Example: `assert(k < index ==> k <= index - 1);` (can be directly justifies by Z3 solver).

- **Redundant**: Remove assertions restate facts already exist in the nearby proofs.
    - Example: The following assertion `assert(2 <= k < n);` should be removed because `assert(2 <= k < n && is_divisible(n as int, k));` already states this fact.
        ```rust
        assert(2 <= k < n && is_divisible(n as int, k));
        assert(2 <= k < n);
        ```

# Input Field

```rust
{{verus_vs}}
```

# Output Field

- If the current Verus program already contains no trivial or redundant proofs, you should only output the verdict `No trivial or redundant proofs.` 

- If there are trivial or redundant Verus proofs, you should: 
    1. Output **exactly** one code snippet enclosed in **```rust** that contains the corresponding Verus code with trivial or redundant content removed.
    2. Output your analysis explaining why you remove these proofs. **Do not include any code enclosed in ```rust in this analysis.**

**CRITICAL REQUIREMENTS:**

- **Do not modify any existing executable code or specifications.**

- **Be conscious when removing a proof. Only remove Trivial and Redundant proofs.**

- Do not introduce `assume()` or `admit()` statements under any circumstances.

- Do not add comments in the program.