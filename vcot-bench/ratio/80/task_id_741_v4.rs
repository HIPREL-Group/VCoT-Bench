use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_exists_witness_from_mismatch(char_arr: &[u8], index: usize)
    requires
        char_arr.len() > 1,
        1 <= index < char_arr.len(),
        char_arr[0] != char_arr[(index as int)],
    ensures
        exists|i: int|
            1 <= i < char_arr@.len() && char_arr[0] != #[trigger] char_arr[i],
{
    let i_int: int = index as int;

    assert(exists|i: int|
        1 <= i < char_arr@.len() && char_arr[0] != #[trigger] char_arr[i]) by {
        assert(1 <= i_int < char_arr@.len() && char_arr[0] != char_arr[i_int]);
    }
}

// Complete the lemma function below
proof fn lemma_forall_up_to_index_implies_forall_1_to_len_when_index_is_len(char_arr: &[u8], index: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn all_characters_same(char_arr: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
{
    if char_arr.len() <= 1 {
        return true;
    }
    let mut index = 1;
    while index < char_arr.len()
        // Fill in loop invariants here
    {
        if char_arr[0] != char_arr[index] {
            // Fill in a block of assertions here to complete the proof;
            return false;
        }
        index += 1;
    }

    // Fill in a block of assertions here to complete the proof

    true
}

} // verus!