use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push_extends_xor_prefix(
    arr1: Seq<i32>,
    arr2: Seq<i32>,
    output_old: Seq<i32>,
    output_new: Seq<i32>,
    index: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        // Fill in loop invariants here
    {
        let output_old = output_arr;
        output_arr = output_old;

        let v = (arr1[index] ^ arr2[index]);

        output_arr.push(v);

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    output_arr
}

} // verus!