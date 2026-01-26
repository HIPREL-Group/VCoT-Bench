use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_split_lt_index_to_lt_index_plus_1(arr: &Vec<i32>, k: i32, index: int)
   

// Complete the lemma function below
proof fn lemma_forall_implies_not_exists<T>(p: spec_fn(T) -> bool)
    

#[verifier::exec_allows_no_decreases_clause]
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] == k) {
            // Fill in a block of assertions here to complete the proof;
            return true;
        }
        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    false
}

} // verus!