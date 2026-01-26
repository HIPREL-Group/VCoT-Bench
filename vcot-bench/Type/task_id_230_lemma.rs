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

    proof {
        assert(out_str@.len() == 0);
        assert(out_str@ == Seq::<u8>::empty());
    }

    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            out_str@.len() == index,
            forall|k: int|
                0 <= k < index ==> out_str[k] == (if str1[k] == 32 {
                    ch
                } else {
                    str1[k]
                }),
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

        assert(out_after == out_before.push(pushed_val));

        proof {
            lemma_push_updates_view(out_before, out_after, pushed_val);

            lemma_push_preserves_prefix_property(
                str1,
                ch,
                out_before,
                out_after,
                (index as int),
            );
        }

        index += 1;
    }

    out_str
}

} // verus!