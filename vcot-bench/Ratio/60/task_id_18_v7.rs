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
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
    {
        if (str[i] == key) {
            proof {
                assert(exists|j: int| 0 <= j < str.len() && (str[j] == key)) by {
                    assert(0 <= (i as int) && (i as int) < str.len() && str[(i as int)] == key);
                }
            }
            return true;
        }

        proof {
            assert(str[i as int] != key);
        }

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
   

proof fn lemma_remove_chars_progress_invariant(
    str1: &[u8],
    str2: &[u8],
    out: Seq<u8>,
    old_index: usize,
    new_index: usize,
    processed: u8,
)
    requires
        new_index == old_index + 1,
        processed == str1[old_index as int],
        forall|k: int|
            0 <= k < old_index ==> (str2@.contains(#[trigger] str1[k]) || out.contains(#[trigger] str1[k])),
        str2@.contains(processed) || out.contains(processed),
    ensures
        forall|k: int|
            0 <= k < new_index ==> (str2@.contains(#[trigger] str1[k]) || out.contains(#[trigger] str1[k])),
{
    assert forall|k: int|
        0 <= k < new_index implies (str2@.contains(#[trigger] str1[k]) || out.contains(#[trigger] str1[k])) by {
        if k < old_index {
            assert(str2@.contains(str1[k]) || out.contains(str1[k]));
        } else {
            assert(k == old_index as int);
            assert(str2@.contains(processed) || out.contains(processed));
        }
    }
}

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
        invariant
            forall|k: int|
                0 <= k < output_str.len() ==> (str1@.contains(#[trigger] output_str[k])
                    && !str2@.contains(#[trigger] output_str[k])),
            forall|k: int|
                0 <= k < index ==> (str2@.contains(#[trigger] str1[k]) || output_str@.contains(
                    #[trigger] str1[k],
                )),
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