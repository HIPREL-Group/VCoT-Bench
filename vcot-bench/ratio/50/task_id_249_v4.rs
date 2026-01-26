use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_range_extend<T>(
    s: Seq<T>,
    key: T,
    i: int,
    j: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= (i as int) <= arr.len(),
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
        if (arr[i] == key) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }
        // Fill in a block of assertions here to complete the proof
        i += 1;
    }
    proof {
        assert(forall|m: int| 0 <= m < arr.len() ==> arr[m] != key) by {
            assert forall|m: int| 0 <= m < arr.len() implies arr[m] != key by {
                assert(0 <= m < (i as int)) by {
                    assert((i as int) == arr.len()) by {
                        assert(!(i < arr.len()));
                        assert((i as int) <= arr.len());
                    }
                }
                assert(arr[m] != key);
            }
        }

        assert(!(exists|k: int| 0 <= k < arr.len() && arr[k] == key)) by {
            assert forall|k: int| 0 <= k < arr.len() implies arr[k] != key by {
                assert(arr[k] != key);
            }
        }
    }
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut output_arr = Vec::new();

    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|i: int|
                0 <= i < output_arr.len() ==> (arr1@.contains(#[trigger] output_arr[i])
                    && arr2@.contains(#[trigger] output_arr[i])),
            forall|m: int, n: int| 0 <= m < n < output_arr.len() ==> output_arr[m] != output_arr[n],
    {
        let ghost x = arr1[(index as int)];
        let in_arr2 = contains(arr2, arr1[index]);
        let in_output = contains(&output_arr, arr1[index]);
        
        if (in_arr2 && !in_output) {
            // Fill in a block of assertions here to complete the proof

            let ghost old_len: int = output_arr.len() as int;
            let ghost old_output_arr = output_arr@;
            output_arr.push(arr1[index]);

            proof {
                let new_len: int = output_arr.len() as int;

                assert(forall|i: int|
                    0 <= i < output_arr.len() ==> (arr1@.contains(output_arr[i]) && arr2@.contains(output_arr[i]))) by {
                    assert forall|i: int| 0 <= i < output_arr.len() implies (arr1@.contains(output_arr[i]) && arr2@.contains(output_arr[i])) by {
                        if i < new_len - 1 {
                            assert(0 <= i < old_len);
                            assert(arr1@.contains(old_output_arr[i]) && arr2@.contains(old_output_arr[i]));
                        } else {
                            assert(i == new_len - 1);
                            let y = output_arr[i];
                            assert(arr2@.contains(y));
                            assert(arr1@.contains(y)) by {
                                assert(arr1@.contains(arr1[(index as int)]));
                            }
                        }
                    }
                }

                assert(forall|m: int, n: int| 0 <= m < n < output_arr.len() ==> output_arr[m] != output_arr[n]) by {
                    assert forall|m: int, n: int| 0 <= m < n < output_arr.len() implies output_arr[m] != output_arr[n] by {
                        if n < output_arr.len() - 1 {
                            assert(old_output_arr[m] != old_output_arr[n]);
                        } else {
                            assert(n == output_arr.len() - 1);
                            assert(0 <= m < output_arr.len() - 1);
                            assert(output_arr[m] != x) by {
                                assert(!old_output_arr.contains(x));
                                assert(old_output_arr[m] == output_arr[m]);
                            }
                        }
                    }
                }
            }
        }
        index += 1;
    }
    output_arr
}

} // verus!