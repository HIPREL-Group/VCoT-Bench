use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_push_preserves_prefix_property(
    str1: &[u8],
    ch: u8,
    out_before: Seq<u8>,
    out_after: Seq<u8>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_push_updates_view(
    before: Seq<u8>,
    after: Seq<u8>,
    x: u8,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn replace_blanks_with_chars(str1: &[u8], ch: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == 32 {
                ch
            } else {
                str1[i]
            }),
{
    let mut out_str: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;

    // Fill in a block of assertions here to complete the proof

    while index < str1.len()
        // Fill in loop invariants here
    {
        let ghost out_before = out_str@;
        assert(out_before.len() == (index as int));

        if (str1[index] == 32) {
            out_str.push(ch);
        } else {
            out_str.push(str1[index]);
        }

        let pushed_val: u8 = if str1[index] == 32 { ch } else { str1[index] };
        let ghost out_after = out_str@;

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    out_str
}

} // verus!