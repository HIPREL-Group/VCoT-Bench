use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn add_list(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] + arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] + arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        // Fill in loop invariants here
    {
        assert(index < arr2.len());

        assert(i32::MIN <= arr1[index as int] + arr2[index as int] <= i32::MAX) by {
            assert(forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] + arr2[i]) <= i32::MAX)
            );
        }

        output_arr.push((arr1[index] + arr2[index]));
        // Fill in a block of assertions here to complete the proof;

        index += 1;

        assert(forall|k: int| 0 <= k < index ==> output_arr[k] == (arr1[k] + arr2[k])) by {
            assert(forall|k: int| 0 <= k < (index - 1) ==> output_arr[k] == (arr1[k] + arr2[k]));
            assert(output_arr[(index - 1) as int] == arr1[(index - 1) as int] + arr2[(index - 1) as int]);
        }
    }
    output_arr
}

} // verus!