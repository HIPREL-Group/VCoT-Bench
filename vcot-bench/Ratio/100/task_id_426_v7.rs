use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_filter_take_succ_u32(s: Seq<u32>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    
    // Fill in a block of assertions here to complete the proof

    while index < arr.len()
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);

            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        index += 1;
    }
    // Fill in a block of assertions here to complete the proof;
    odd_list
}

}