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
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|k: int|
                0 <= k < index ==> output_arr[k] == #[trigger] arr1[k] ^ #[trigger] arr2[k],
    {
        let output_old = output_arr;
        output_arr = output_old;

        let v = (arr1[index] ^ arr2[index]);

        output_arr.push(v);

        proof {
            let new_view = output_arr@;
            let old_view = new_view.subrange(0, index as int);

            assert(old_view.len() == index as int);
            assert(new_view.len() == index as int + 1);

            assert(forall|k: int| 0 <= k < index as int ==> old_view[k] == arr1[k] ^ arr2[k]);

            assert(new_view == old_view.push(arr1[index as int] ^ arr2[index as int]));

            lemma_vec_push_extends_xor_prefix(arr1@, arr2@, old_view, new_view, index as int);
        }

        index += 1;
    }
    output_arr
}

} // verus!