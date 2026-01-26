use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_prefix_extend_i32(arr: &Vec<i32>, element: i32, n: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut index = 0;

    while index < arr.len()
        // Fill in loop invariants here
    {
        if arr[index] != element {
            // Fill in a block of assertions here to complete the proof

            return false;
        }

        let old_index = index;
        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    // Fill in a block of assertions here to complete the proof

    true
}

} // verus!