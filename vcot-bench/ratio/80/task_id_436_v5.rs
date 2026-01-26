use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_succ(arr: Seq<i32>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_take_step(arr: Seq<i32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    assert(arr@ == arr@.take(input_len as int));
    negative_list
}

}