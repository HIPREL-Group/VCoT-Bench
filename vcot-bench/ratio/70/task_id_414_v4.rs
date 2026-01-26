use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
        if (arr[i] == key) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }
        i += 1;
    }
    // Fill in a block of assertions here to complete the proof
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    let mut index = 0;
    while index < arr1.len()
        // Fill in loop invariants here
    {
        if (contains(arr2, arr1[index])) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }
        index += 1;
    }

    proof {
        assert(!(exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k]))) by {
            assert(forall|k: int| 0 <= k < arr1.len() ==> !arr2@.contains(arr1[k]));
        }

        assert(!(exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]))) by {
            assert(!(exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k])));
        }
    }

    false
}

} // verus!