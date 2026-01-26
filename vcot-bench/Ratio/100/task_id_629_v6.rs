use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_take_succ_drop_last<T>(s: Seq<T>, i: int)
   

// Complete the lemma function below
proof fn lemma_take_all<T>(s: Seq<T>)
    

#[verifier::exec_allows_no_decreases_clause]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    // Fill in a block of assertions here to complete the proof;

    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }

        // Fill in a block of assertions here to complete the proof
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;
    even_numbers
}

} // verus!