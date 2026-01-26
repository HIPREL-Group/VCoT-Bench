use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_eq<T>(
    index: int,
    output_arr: &Vec<T>,
    arr1: &Vec<T>,
    arr2: &Vec<T>,
    new_val: T,
)
   

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
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        let prev_len: usize = output_arr.len();

        output_arr.push((arr1[index] / arr2[index]));

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    output_arr
}

} // verus!