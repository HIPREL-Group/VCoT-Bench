use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_range_extend<T>(
    s: Seq<T>,
    key: T,
    i: int,
    j: int,
)
    requires
        0 <= i <= j,
        forall|m: int| 0 <= m < i ==> s[m] != key,
        forall|m: int| i <= m < j ==> s[m] != key,
    ensures
        forall|m: int| 0 <= m < j ==> s[m] != key,
{
    assert(forall|m: int| 0 <= m < j ==> s[m] != key) by {
        assert forall|m: int| 0 <= m < j implies s[m] != key by {
            if m < i {
                assert(0 <= m < i);
                assert(s[m] != key);
            } else {
                assert(i <= m < j);
                assert(s[m] != key);
            }
        }
    }
}

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
                assert(exists|k: int| 0 <= k < arr.len() && arr[k] == key) by {
                    assert(0 <= (i as int) && i < arr.len() && arr[(i as int)] == key);
                }
            }
            return true;
        }
        proof {
            let ip1: int = (i as int) + 1;

            assert(forall|m: int| 0 <= m < ip1 ==> arr[m] != key) by {
                assert forall|m: int| 0 <= m < ip1 implies arr[m] != key by {
                    if m < (i as int) {
                        assert(0 <= m < (i as int));
                        assert(arr[m] != key);
                    } else {
                        assert(m == (i as int));
                        assert(arr[(i as int)] != key);
                    }
                }
            }
        }
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
        // Fill in loop invariants here
    {
        let ghost x = arr1[(index as int)];
        let in_arr2 = contains(arr2, arr1[index]);
        let in_output = contains(&output_arr, arr1[index]);
        
        if (in_arr2 && !in_output) {
            proof {
                assert(arr2@.contains(x)) by {
                    assert(in_arr2);
                    assert(exists|i: int| 0 <= i < arr2.len() && arr2[i] == x);
                }
                assert(!output_arr@.contains(x)) by {
                    assert(!in_output);
                    assert(!(exists|i: int| 0 <= i < output_arr.len() && output_arr[i] == x));
                }

                let old_len: int = output_arr.len() as int;

                assert(forall|i: int| 0 <= i < old_len ==> output_arr[i] != x) by {
                    assert forall|i: int| 0 <= i < old_len implies output_arr[i] != x by {
                        assert(!output_arr@.contains(x));
                        if output_arr[i] == x {
                            assert(output_arr@.contains(x)) by {
                                assert(0 <= i < output_arr.len());
                            }
                        }
                    }
                }

                assert(forall|i: int| 0 <= i < output_arr.len() ==> output_arr[i] != x) by {
                    assert(output_arr.len() as int == old_len);
                    lemma_forall_range_extend(output_arr@, x, old_len, output_arr.len() as int);
                }

                assert(output_arr.len() == old_len);
            }

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