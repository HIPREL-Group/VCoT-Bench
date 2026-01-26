use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_extend_no_odd_prefix(v: &Vec<u64>, j: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut j: usize = 0;

    while (j < v.len())
    // Fill in loop invariants here
    {
        if (v[j] % 2 == 1) {
            return j;
        }

        // Fill in a block of assertions here to complete the proof;

        j = j + 1;
    }

    // Fill in a block of assertions here to complete the proof
    j
}

}