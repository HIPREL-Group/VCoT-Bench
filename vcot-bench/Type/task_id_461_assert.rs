use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn count_uppercase_recursively(seq: Seq<u8>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

proof fn lemma_subrange_drop_last_equiv(s: Seq<u8>, i: int)
    requires
        1 <= i,
        i <= s.len(),
    ensures
        s.subrange(0, i - 1) == s.subrange(0, i).drop_last(),
{
    let t = s.subrange(0, i);

    assert(t.len() == i) by {
        assert(t.len() == i - 0);
    }
    assert(t.len() >= 1);
    assert(t.len() - 1 == i - 1);

    assert(t.drop_last() == t.subrange(0, t.len() - 1));

    assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1)) by {
        assert(t.len() - 1 == i - 1);
        assert(t.subrange(0, t.len() - 1) =~= s.subrange(0, i - 1));
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn count_uppercase(text: &[u8]) -> (count: u64)
    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
{
    let mut index = 0;
    let mut count = 0;

    while index < text.len()
        invariant
            0 <= index <= text.len(),
            0 <= count <= index,
            count_uppercase_recursively(text@.subrange(0, (index as int))) == count,
    {
        let old_index = index;
        let old_count = count;

        let ghost prefix_before = text@.subrange(0, (old_index as int));
        let c = text[old_index];
        // Fill in a block of assertions here to complete the proof;

        if (text[old_index] >= 65 && text[old_index] <= 90) {
            // Fill in a block of assertions here to complete the proof;
            count += 1;
        } else {
            // Fill in a block of assertions here to complete the proof;
        }

        index += 1;

        let ghost prefix_after = text@.subrange(0, (index as int));

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof
    count
}

} // verus!