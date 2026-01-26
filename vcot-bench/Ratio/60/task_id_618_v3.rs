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
   

proof fn lemma_forall_u32_nonzero_inst(arr2: &Vec<u32>, i: int)
    requires
        forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
        0 <= i < arr2.len(),
    ensures
        arr2[i] != 0,
{
    lemma_forall_range_to_index((arr2.len() as int), i, |j: int| arr2[j] != 0);
}

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
        // Fill in loop invariants here
    {
        assert(arr2[(index as int)] != 0) by {
            lemma_forall_u32_nonzero_inst(arr2, (index as int));
        }

        assert(i32::MIN <= (arr1[(index as int)] / arr2[(index as int)]) <= i32::MAX) by {
            lemma_forall_u32_div_bounds_inst(arr1, arr2, (index as int));
        }

        let x = (arr1[index] / arr2[index]);
        output_arr.push(x);

        index += 1;
    }

    output_arr
}

} // verus!