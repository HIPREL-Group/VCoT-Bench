use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take0_filter_empty(arr: Seq<u32>)
    

// Complete the lemma function below
proof fn lemma_take_drop_last(arr: Seq<u32>, i: int)
   

// Complete the lemma function below
proof fn lemma_take_len_full(arr: Seq<u32>)
    

// Complete the lemma function below
proof fn lemma_take_succ_push(arr: Seq<u32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] % 2 == 0) {
            even_list.push(arr[index]);
        }

        // Fill in a block of assertions here to complete the proof

        if arr[index] % 2 == 0 {
            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    even_list
}

}