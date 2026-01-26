use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_drop_last_step_u32(arr: Seq<u32>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_append_u32(s1: Seq<u32>, s2: Seq<u32>)
    

// Complete the lemma function below
proof fn lemma_filter_push_u32(s: Seq<u32>, x: u32)
    

#[verifier::exec_allows_no_decreases_clause]
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);

            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        index += 1;
    }
    // Fill in a block of assertions here to complete the proof;
    odd_numbers
}

}