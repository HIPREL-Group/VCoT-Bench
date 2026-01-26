use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_push_extends_pointwise(
    old_s: Seq<u32>,
    new_s: Seq<u32>,
    idx: usize,
    elem: u32,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
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
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] % arr2[k]),
    {
        assert(arr2[(index as int)] != 0);

        let v = arr1[index] % arr2[index];

        assert(i32::MIN <= (arr1[(index as int)] % arr2[(index as int)]) <= i32::MAX);

        output_arr.push((arr1[index] % arr2[index]));

        proof {
            let old_view = output_arr@.subrange(0, (index as int));
            assert(output_arr@[index as int] == v);

            assert(forall|k: int| 0 <= k < (index as int) ==> output_arr[k] == old_view[k]);

            assert(forall|k: int|
                0 <= k < index + 1 ==> output_arr[k] == (arr1[k] % arr2[k])) by {
                assert forall|k: int| 0 <= k < index + 1 implies output_arr[k] == (arr1[k] % arr2[k]) by {
                    if k == (index as int) {
                        assert(output_arr[k] == v);
                    }
                }
            }
        }

        index += 1;
    }

    output_arr
}

}