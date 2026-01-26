use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

// Complete the lemma function below
proof fn lemma_exists_intro_divisor(n: u64, k: u64)
   

// Complete the lemma function below
proof fn lemma_no_divisor_prefix_extend(n: int, i: u64)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    if n <= 1 {
        return true;
    }
    let mut index = 2;
    while index < n
        // Fill in loop invariants here
    {
        if ((n % index) == 0) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }
        // Fill in a block of assertions here to complete the proof
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof
    false
}

} // verus!