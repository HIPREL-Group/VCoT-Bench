use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_range_to_index(
    n: int,
    i: int,
    p: spec_fn(int) -> bool,
)
   

// Complete the lemma function below
proof fn lemma_forall_u32_div_bounds_inst(arr1: &Vec<u32>, arr2: &Vec<u32>, i: int)
   

// Complete the lemma function below
proof fn lemma_forall_u32_nonzero_inst(arr2: &Vec<u32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
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
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] / arr2[k]),
    {
        // Fill in a block of assertions here to complete the proof

        let x = (arr1[index] / arr2[index]);
        output_arr.push(x);

        index += 1;
    }

    output_arr
}

} // verus!