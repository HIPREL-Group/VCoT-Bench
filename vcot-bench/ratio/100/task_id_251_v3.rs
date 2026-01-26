use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_insert_before_each_step(
    arr: &Vec<i32>,
    elem: i32,
    result_old: Seq<i32>,
    index: int,
    result_new: Seq<i32>,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        // Fill in loop invariants here
    {
        let ghost old_seq = result@;

        result.push(elem);
        result.push(arr[index]);

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    result
}

} // verus!