use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_seq_push_extensional_i32(s: Seq<i32>, x: i32)
    

#[verifier::exec_allows_no_decreases_clause]
fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] * arr2[i]),
{
    let mut output_arr = Vec::with_capacity(arr1.len());
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= index <= arr2.len(),
            output_arr.len() == index,
            forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
            forall|k: int|
                0 <= k < index ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] * arr2[k]),
    {
        assert(i32::MIN <= arr1[(index as int)] * arr2[(index as int)] <= i32::MAX) by {
            assert(forall|i: int|
                (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX));
            assert(0 <= index < arr1.len());
        }

        let ghost old_len: int = (output_arr.len() as int);

        let x = arr1[index] * arr2[index];

        output_arr.push(x);

        assert(output_arr.len() == old_len + 1) by {
            assert(output_arr@.len() == (output_arr.len() as int));
        }

        assert(forall|k: int|
            0 <= k < index + 1 ==> #[trigger] output_arr[k] == #[trigger] (arr1[k] * arr2[k])) by {
            assert forall|k: int| 0 <= k < index + 1 implies output_arr[k] == (arr1[k] * arr2[k]) by {
                if 0 <= k < index + 1 {
                    if k < index {
                        assert(output_arr[k] == arr1[k] * arr2[k]);
                    } else {
                        assert(k == index);
                        assert(output_arr[old_len] == x);
                        assert(x == arr1[(index as int)] * arr2[(index as int)]);
                    }
                }
            }
        }

        index += 1;
    }
    output_arr
}

} // verus!