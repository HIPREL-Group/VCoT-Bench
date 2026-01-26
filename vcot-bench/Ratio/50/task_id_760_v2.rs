use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() <= 1 {
        return true;
    }
    let mut index = 1;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if arr[0] != arr[index] {
            assert(exists|i: int| 1 <= i < arr@.len() && arr[0] != #[trigger] arr[i]) by {
                let i: int = index as int;
                assert(i < arr@.len());
                assert(arr[0] != #[trigger] arr[i]);
            };

            return false;
        }

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    assert(forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]) by {
        assert(forall|k: int| 0 <= k < index ==> arr[0] == #[trigger] arr[k]);
    };

    true
}

} // verus!