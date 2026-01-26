use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_seq_push_preserves_prefix_u64(s: Seq<u64>, x: u64)
    

#[verifier::exec_allows_no_decreases_clause]
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;

    while index < arr.len()
        // Fill in loop invariants here
    {
        let ghost old_copied_view = copied_array@;
        let x = arr[index];

        copied_array.push(x);

        // Fill in a block of assertions here to complete the proof;

        index += 1;

        assert(copied_array.len() == index);
    }

    // Fill in a block of assertions here to complete the proof

    copied_array
}

} // verus!