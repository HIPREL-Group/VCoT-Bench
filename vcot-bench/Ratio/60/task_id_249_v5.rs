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
            // Fill in a block of assertions here to complete the proof
            return true;
        }
        // Fill in a block of assertions here to complete the proof
        i += 1;
    }
    // Fill in a block of assertions here to complete the proof
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

            // Fill in a block of assertions here to complete the proof
        }
        index += 1;
    }
    output_arr
}

} // verus!