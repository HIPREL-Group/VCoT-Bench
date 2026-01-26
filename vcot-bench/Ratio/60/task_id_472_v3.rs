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
        invariant
            0 <= index <= arr.len() - 1,
            forall|k: int| 0 <= k < arr.len() ==> (0 <= #[trigger] arr[k] + 1 < i32::MAX),
            forall|k: int, l: int| (0 <= k < l <= index && l == k + 1) ==> (arr[k] + 1 == arr[l]),
    {
        if (arr[index] + 1 != arr[index + 1]) {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    assert(index == arr.len() - 1) by {
        assert(!(index < arr.len() - 1));
        assert(0 <= index <= arr.len() - 1);
    }

    assert(forall|i: int, j: int|
        0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])
    ) by {
        assert forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 implies (arr[i] + 1 == arr[j])
        by {
            if 0 <= i < j < arr.len() && j == i + 1 {
                assert(j <= index);
                assert(0 <= i < j <= index && j == i + 1);
                assert(arr[i] + 1 == arr[j]);
            }
        }
    };

    true
}

} // verus!