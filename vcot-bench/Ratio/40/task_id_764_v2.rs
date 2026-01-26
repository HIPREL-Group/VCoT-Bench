use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_digit(c: u8) -> bool {
    (c >= 48 && c <= 57)
}

spec fn count_digits_recursively(seq: Seq<u8>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_digits_recursively(seq.drop_last()) + if is_digit(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

proof fn lemma_subrange_drop_last_eq<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i <= s.len(),
        i > 0,
    ensures
        s.subrange(0, i - 1) == s.subrange(0, i).drop_last(),
{
    let t = s.subrange(0, i);
    assert(t.len() == i);

    assert(t.drop_last() == t.subrange(0, t.len() - 1)) by {
        assert(t.drop_last() =~= t.subrange(0, t.len() - 1));
    }

    assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1)) by {
        assert(t.subrange(0, t.len() - 1) =~= s.subrange(0, i - 1));
    }

    assert(t.drop_last() == s.subrange(0, i - 1));

    assert(t == s.subrange(0, i));
    assert(t.drop_last() == s.subrange(0, i).drop_last());
    assert(s.subrange(0, i - 1) == s.subrange(0, i).drop_last());
}

proof fn lemma_seq_subrange_last_is_original_index<T>(s: Seq<T>, i: int)
    requires
        0 < i,
        i <= s.len(),
    ensures
        s.subrange(0, i).last() == s[i - 1],
{
    let t = s.subrange(0, i);
    assert(t.len() == i);

    assert(t.last() == t.index(t.len() - 1)) by {
        assert(t.last() =~= t.index(t.len() - 1));
    }
    assert(t.len() - 1 == i - 1);
    assert(t.index(i - 1) == s[i - 1]) by {
        assert(t.index(i - 1) =~= s.index((i - 1) + 0));
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn count_digits(text: &[u8]) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut index = 0;

    while index < text.len()
        // Fill in loop invariants here
    {
        if (text[index] >= 48 && text[index] <= 57) {
            count += 1;
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    assert(text@ == text@.subrange(0, index as int));
    count
}

}