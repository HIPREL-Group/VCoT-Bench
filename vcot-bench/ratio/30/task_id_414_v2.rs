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
        // Fill in loop invariants here
    {
        if (arr[i] == key) {
            proof {
                assert(exists|w: int| 0 <= w < arr.len() && arr[w] == key) by {
                    assert(arr[(i as int)] == key);
                }
            }
            return true;
        }
        i += 1;
    }
    proof {
        assert(!(exists|j: int| 0 <= j < arr.len() && arr[j] == key)) by {
            assert(forall|m: int| 0 <= m < arr.len() ==> arr[m] != key);
        }
    }
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|k: int| 0 <= k < index ==> !arr2@.contains(#[trigger] arr1[k]),
    {
        if (contains(arr2, arr1[index])) {
            proof {
                assert(exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k])) by {
                    assert(arr2@.contains(arr1[(index as int)]));
                    assert(0 <= index < arr1.len());
                }
            }
            return true;
        }
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof

    false
}

} // verus!