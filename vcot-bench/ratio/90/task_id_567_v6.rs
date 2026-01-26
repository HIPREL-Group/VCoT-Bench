use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_sorted_extend_by_one(arr: &Vec<i32>, index: int)
   

// Complete the lemma function below
proof fn lemma_sorted_prefix_to_total_when_finished(arr: &Vec<i32>, index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut index = 0;
    while index < arr.len() - 1
        // Fill in loop invariants here
    {
        if arr[index] > arr[index + 1] {
            // Fill in a block of assertions here to complete the proof
            return false;
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    assert(index == arr.len() - 1) by {
        assert(index <= arr.len() - 1);
        assert(!(index < arr.len() - 1));
    }

    proof {
        lemma_sorted_prefix_to_total_when_finished(arr, (index as int));
    }

    true
}

} // verus!