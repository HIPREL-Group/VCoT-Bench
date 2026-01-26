use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        // Fill in loop invariants here
    {
        if (str[i] == key) {
            proof {
                assert(exists|j: int| 0 <= j < str.len() && (str[j] == key)) by {
                    assert(0 <= (i as int) && (i as int) < str.len() && str[(i as int)] == key);
                }
            }
            return true;
        }

        // Fill in a block of assertions here to complete the proof

        i += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

    false
}

// Complete the lemma function below
proof fn lemma_remove_chars_push_preserves_invariant(
    str1: &[u8],
    str2: &[u8],
    old_out: Seq<u8>,
    old_index: usize,
    new_out: Seq<u8>,
    x: u8,
)
   

// Complete the lemma function below
proof fn lemma_remove_chars_progress_invariant(
    str1: &[u8],
    str2: &[u8],
    out: Seq<u8>,
    old_index: usize,
    new_index: usize,
    processed: u8,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn remove_chars(str1: &[u8], str2: &[u8]) -> (result: Vec<u8>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    let ghost mut output_len: int = 0;

    while index < str1.len()
        // Fill in loop invariants here
    {
        if (!contains(str2, str1[index])) {
            // Fill in a block of assertions here to complete the proof
            output_str.push(str1[index]);
        } else {
            // Fill in a block of assertions here to complete the proof
        }
        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    output_str
}

} // verus!