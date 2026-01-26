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
        invariant
            0 <= index <= s.len(),
            rear_chars.len() == index,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() > 0,
            forall|k: int| 0 <= k < index ==> rear_chars[k] == #[trigger] s[k][s[k].len() - 1],
    {
        let seq = &s[index];

        // Fill in a block of assertions here to complete the proof;

        let last = seq[seq.len() - 1];

        // Fill in a block of assertions here to complete the proof;

        let old_index = index;
        let old_rear_len = rear_chars.len();

        rear_chars.push(last);

        assert(rear_chars[old_index as int] == s[old_index as int][s[old_index as int].len() - 1]) by {
            assert(old_rear_len == old_index);
        };

        index += 1;
    }

    rear_chars
}

} // verus!