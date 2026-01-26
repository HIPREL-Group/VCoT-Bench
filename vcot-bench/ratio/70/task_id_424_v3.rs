use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn extract_rear_chars(s: &Vec<Vec<u8>>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> result[i] == #[trigger] s[i][s[i].len() - 1],
{
    let mut rear_chars: Vec<u8> = Vec::with_capacity(s.len());
    let mut index = 0;

    while index < s.len()
        // Fill in loop invariants here
    {
        let seq = &s[index];

        // Fill in a block of assertions here to complete the proof;

        let last = seq[seq.len() - 1];

        assert(last == s[(index as int)][s[(index as int)].len() - 1]) by {
            assert(seq == &s[(index as int)]);
        };

        let old_index = index;
        let old_rear_len = rear_chars.len();

        rear_chars.push(last);

        // Fill in a block of assertions here to complete the proof;

        index += 1;
    }

    rear_chars
}

} // verus!