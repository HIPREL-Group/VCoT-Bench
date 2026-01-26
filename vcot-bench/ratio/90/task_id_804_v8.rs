use vstd::prelude::*;
fn main() {
}

verus! {

spec fn is_even(n: u32) -> bool {
    (n % 2) == 0
}

// Complete the lemma function below
proof fn lemma_forall_split_at_index(arr: &Vec<u32>, index: int)
   

// Complete the lemma function below
proof fn lemma_forall_prefix_from_index_plus_1(
    arr: &Vec<u32>,
    old_index: int,
    new_index: int,
)
   

// Complete the lemma function below
proof fn lemma_not_exists_from_forall_not(
    arr: &Vec<u32>,
    n: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    let mut index = 0;

    // Fill in a block of assertions here to complete the proof

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> !(is_even(#[trigger] arr[k])),
    {
        if (arr[index] % 2 == 0) {
            // Fill in a block of assertions here to complete the proof

            return true;
        }

        // Fill in a block of assertions here to complete the proof

        let old_index = index;
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

    false
}

} // verus!