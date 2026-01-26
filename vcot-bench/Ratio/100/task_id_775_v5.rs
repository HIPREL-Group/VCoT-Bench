use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_extend_prefix_parity(arr: &Vec<usize>, index: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if ((index % 2) != (arr[index] % 2)) {
            // Fill in a block of assertions here to complete the proof

            return false;
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof

    true
}

} // verus!