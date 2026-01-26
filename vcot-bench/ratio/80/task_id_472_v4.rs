use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_consecutive_prefix_extend(arr: &Vec<i32>, index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while (index < arr.len() - 1)
        // Fill in loop invariants here
    {
        if (arr[index] + 1 != arr[index + 1]) {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }

        proof {
            lemma_consecutive_prefix_extend(arr, (index as int));
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    true
}

} // verus!