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

// Complete the lemma function below
proof fn lemma_subrange_drop_last_eq<T>(s: Seq<T>, i: int)
   

// Complete the lemma function below
proof fn lemma_seq_subrange_last_is_original_index<T>(s: Seq<T>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn count_digits(text: &[u8]) -> (count: usize)
    ensures
        0 <= count <= text.len(),
        count_digits_recursively(text@) == count,
{
    let mut count = 0;
    let mut index = 0;

    while index < text.len()
        invariant
            0 <= index <= text.len(),
            0 <= count <= index,
            count == count_digits_recursively(text@.subrange(0, index as int)),
    {
        if (text[index] >= 48 && text[index] <= 57) {
            count += 1;
        }
        index += 1;

        proof {
            lemma_subrange_drop_last_eq(text@, index as int);
        }

        assert(text@.subrange(0, index as int).last() == text@[index - 1]) by {
            lemma_seq_subrange_last_is_original_index(text@, index as int);
            assert(text@.subrange(0, index as int).last() == text@[(index as int) - 1]);
        }

        assert(is_digit(text@[index - 1]) == (text[index - 1] >= 48 && text[index - 1] <= 57)) by {
            assert(text@[index - 1] == text[index - 1]);
        }

        assert(count_digits_recursively(text@.subrange(0, index as int))
            == count_digits_recursively(text@.subrange(0, (index - 1) as int))
                + if is_digit(text@[index - 1]) { 1int } else { 0int }) by
        {
            let s1 = text@.subrange(0, index as int);
            assert(s1.drop_last() == text@.subrange(0, (index - 1) as int));
            assert(s1.last() == text@[index - 1]);
        }
    }
    assert(text@ == text@.subrange(0, index as int));
    count
}

}