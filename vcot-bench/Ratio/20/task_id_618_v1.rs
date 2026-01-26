use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_range_to_index(
    n: int,
    i: int,
    p: spec_fn(int) -> bool,
)
    requires
        forall|k: int| 0 <= k < n ==> #[trigger] p(k),
        0 <= i < n,
    ensures
        p(i),
{
}

proof fn lemma_forall_u32_div_bounds_inst(arr1: &Vec<u32>, arr2: &Vec<u32>, i: int)
    requires
        arr1.len() == arr2.len(),
        forall|j: int|
            (0 <= j < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[j] / arr2[j]) <= i32::MAX),
        0 <= i < arr1.len(),
    ensures
        i32::MIN <= (arr1[i] / arr2[i]) <= i32::MAX,
{
    lemma_forall_range_to_index(
        (arr1.len() as int),
        i,
        |j: int| i32::MIN <= (arr1[j] / arr2[j]) <= i32::MAX,
    );
}

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