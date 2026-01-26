use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_seq_push_preserves_prefix_u64(s: Seq<u64>, x: u64)
    ensures
        forall|i: int| (0 <= i < s.len()) ==> s[i] == s.push(x)[i],
{
    assert forall|i: int| (0 <= i < s.len()) implies s[i] == s.push(x)[i] by {
        assert(i != s.len());
        assert(s.push(x)[i] == s[i]);
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied_array = Vec::with_capacity(arr.len());
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            copied_array.len() == index,
            forall|i: int| (0 <= i < index) ==> arr[i] == copied_array[i],
    {
        let ghost old_copied_view = copied_array@;
        let x = arr[index];

        copied_array.push(x);

        // Fill in a block of assertions here to complete the proof;

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    // Fill in a block of assertions here to complete the proof

    copied_array
}

} // verus!