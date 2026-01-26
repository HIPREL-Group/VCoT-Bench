use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend(arr1: &Vec<i32>, arr2: &Vec<i32>, i: int)
   

proof fn lemma_exists_counterexample_from_prefix_violation(
    arr1: &Vec<i32>,
    arr2: &Vec<i32>,
    index: int,
)
    requires
        arr1.len() == arr2.len(),
        0 <= index < arr1.len(),
        !(arr1[index] > arr2[index]),
    ensures
        !(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    assert(!(forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i])) by {
        let i = index;
        assert(!(arr1[i] > arr2[i]));
    };
}

// Complete the lemma function below
proof fn lemma_forall_from_prefix_at_end(arr1: &Vec<i32>, arr2: &Vec<i32>, index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut index = 0;
    while index < arr1.len()
        // Fill in loop invariants here
    {
        if arr1[index] <= arr2[index] {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }
        // Fill in a block of assertions here to complete the proof;

        let old_index = index;
        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }
    // Fill in a block of assertions here to complete the proof;
    true
}

} // verus!