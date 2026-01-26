use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_extend_at_index(
    str1: &[u8],
    old_char: u8,
    new_char: u8,
    result_str: &Vec<u8>,
    index: int,
    v: u8,
)
    requires
        0 <= index,
        result_str@.len() == index + 1,
        result_str[index] == v,
        v == (if str1[index] == old_char { new_char } else { str1[index] }),
        forall|k: int|
            0 <= k < index ==> result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }),
    ensures
        forall|k: int|
            0 <= k < index + 1 ==> result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }),
{
    assert forall|k: int|
        0 <= k < index + 1 ==>
            result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] })
    by {
        if 0 <= k && k < index + 1 {
            if k < index {
                assert(result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }));
            } else {
                assert(k == index);
                assert(result_str[k] == result_str[index]);
                assert(result_str[index] == v);
                assert(v == (if str1[index] == old_char { new_char } else { str1[index] }));
                assert(result_str[k] == (if str1[k] == old_char { new_char } else { str1[k] }));
            }
        }
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn replace_chars(str1: &[u8], old_char: u8, new_char: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == old_char {
                new_char
            } else {
                str1[i]
            }),
{
    let mut result_str = Vec::with_capacity(str1.len());
    let mut index = 0;

    while index < str1.len()
        invariant
            0 <= index <= str1@.len(),
            result_str@.len() == index,
            forall|k: int|
                0 <= k < index ==> result_str[k] == (if str1[k] == old_char {
                    new_char
                } else {
                    str1[k]
                }),
    {
        let v: u8;
        if str1[index] == old_char {
            v = new_char;
            result_str.push(new_char);
        } else {
            v = str1[index];
            result_str.push(str1[index]);
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    result_str
}

} // verus!