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

// Complete the lemma function below
proof fn lemma_subrange_drop_last_equiv(s: Seq<u8>, i: int)
   

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
            assert(is_upper_case(c));
            count += 1;
        } else {
            assert(!is_upper_case(c));
        }

        index += 1;

        let ghost prefix_after = text@.subrange(0, (index as int));

        // Fill in a block of assertions here to complete the proof
    }

    assert(text@ == text@.subrange(0, (index as int))) by {
        assert(index == text.len());
        assert(text@.subrange(0, (text@.len() as int)) == text@);
    }
    count
}

} // verus!