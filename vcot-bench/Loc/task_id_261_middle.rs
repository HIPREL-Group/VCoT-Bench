use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_extend_by_one_eq<T>(
    index: int,
    output_arr: &Vec<T>,
    arr1: &Vec<T>,
    arr2: &Vec<T>,
    new_val: T,
)
    requires
        0 <= index,
        output_arr.len() == index,
        forall|k: int| 0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k]),
        new_val == arr1[index],
    ensures
        forall|k: int| 0 <= k < index + 1 ==> (if k < index { output_arr[k] } else { new_val })
            == #[trigger] arr1[k],
{
    assert(forall|k: int| 0 <= k < index + 1 ==> (if k < index { output_arr[k] } else { new_val })
        == #[trigger] arr1[k]) by {
        assert(forall|k: int|
            0 <= k < index + 1 ==> (if k < index { output_arr[k] } else { new_val })
                == #[trigger] arr1[k]) by {
            assert forall|k: int|
                0 <= k < index + 1 implies (if k < index { output_arr[k] } else { new_val })
                    == #[trigger] arr1[k]
            by {
                if k < index {
                    assert(output_arr[k] == arr1[k]) by {
                        assert(forall|kk: int| 0 <= kk < index ==> output_arr[kk] == arr1[kk]);
                    }
                    assert((if k < index { output_arr[k] } else { new_val }) == arr1[k]);
                } else {
                    assert(k == index) by {
                        assert(k < index + 1);
                        assert(!(k < index));
                        assert(k >= index);
                        assert(k <= index) by {
                            assert(k < index + 1);
                        }
                    }
                    assert((if k < index { output_arr[k] } else { new_val }) == new_val);
                    assert(new_val == arr1[index]);
                    assert(arr1[k] == arr1[index]) by {
                        assert(k == index);
                    }
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());

    let mut index = 0;

    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
            forall|m: int|
                0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                    <= u32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] / arr2[k]),
    {
        // Fill in a block of assertions here to complete the proof

        let prev_len: usize = output_arr.len();

        output_arr.push((arr1[index] / arr2[index]));

        assert(output_arr.len() == prev_len + 1);

        assert(forall|k: int|
            0 <= k < index + 1 ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] / arr2[k])) by {
            assert(forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] / arr2[k]));
            assert forall|k: int|
                0 <= k < index + 1 implies #[trigger] output_arr[k] == #[trigger] (arr1[k] / arr2[k])
            by {
                if k < index {
                    assert(output_arr[k] == arr1[k] / arr2[k]);
                } else {
                    assert(k == index) by {
                        assert(!(k < index));
                        assert(k < index + 1);
                        assert(k >= index);
                        assert(k <= index) by {
                            assert(k < index + 1);
                        }
                    }
                    assert(output_arr.len() == index + 1);
                    assert(output_arr[(index as int)] == arr1[(index as int)] / arr2[(index as int)]);
                    assert(output_arr[k] == arr1[k] / arr2[k]) by {
                        assert(k == index);
                    }
                }
            }
        }

        index += 1;
    }
    output_arr
}

} // verus!