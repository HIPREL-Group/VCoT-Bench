use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend(arr: &Vec<i32>, number: i32, i: int)
   

proof fn lemma_not_forall_from_counterexample(arr: &Vec<i32>, number: i32, j: int)
    requires
        0 <= j,
        j < arr.len(),
        !(number > arr[j]),
    ensures
        !(forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
}

#[verifier::exec_allows_no_decreases_clause]
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut i = 0;

    while i < arr.len()
        // Fill in loop invariants here
    {
        if number <= arr[i] {
            // Fill in a block of assertions here to complete the proof
            return false;
        }
        // Fill in a block of assertions here to complete the proof

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof
    true
}

} // verus!