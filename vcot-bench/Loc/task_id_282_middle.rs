use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());

    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] - arr2[k]),
    {
        // Fill in a block of assertions here to complete the proof;

        output_arr.push((arr1[index] - arr2[index]));

        assert(output_arr.len() == index + 1);

        assert(forall|k: int| 0 <= k < index ==> output_arr[k] == arr1[k] - arr2[k]);
        assert(output_arr[index as int] == arr1[index as int] - arr2[index as int]);

        assert(forall|k: int|
            0 <= k < (index + 1) ==> output_arr[k] == arr1[k] - arr2[k]) by {
            assert(forall|k: int| 0 <= k < index ==> output_arr[k] == arr1[k] - arr2[k]);
            assert(output_arr[index as int] == arr1[index as int] - arr2[index as int]);

            assert(forall|k: int|
                0 <= k < (index + 1) ==> output_arr[k] == arr1[k] - arr2[k]) by {
                assert(forall|k: int|
                    0 <= k < (index + 1) ==> output_arr[k] == arr1[k] - arr2[k]) by {
                    assert(forall|k: int|
                        0 <= k < (index + 1) ==> output_arr[k] == arr1[k] - arr2[k]);
                };
            };
        };

        index += 1;
    }
    output_arr
}

} // verus!