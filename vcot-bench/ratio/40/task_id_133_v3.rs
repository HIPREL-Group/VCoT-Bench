use vstd::prelude::*;

fn main() {
}

verus! {

spec fn sum_negative_to(seq: Seq<i64>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

proof fn lemma_len_drop_last(s: Seq<i64>)
    requires
        s.len() >= 1,
    ensures
        s.drop_last().len() == s.len() - 1,
{
}

proof fn lemma_subrange_drop_last_eq(s: Seq<i64>, k: int)
    requires
        1 <= k <= s.len(),
    ensures
        s.subrange(0, k - 1) == s.subrange(0, k).drop_last(),
{
    assert(s.subrange(0, k - 1) =~= s.subrange(0, k).drop_last());
}

proof fn lemma_sum_negative_to_step(arr: Seq<i64>, k: int)
    requires
        1 <= k <= arr.len(),
    ensures
        sum_negative_to(arr.subrange(0, k))
        == sum_negative_to(arr.subrange(0, k - 1))
            + if arr[k - 1] < 0 { arr[k - 1] as int } else { 0int },
{
    let s = arr.subrange(0, k);
    lemma_subrange_drop_last_eq(arr, k);
    assert(s.last() == arr[k - 1]);
}

#[verifier::exec_allows_no_decreases_clause]
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;

    while index < arr.len()
        // Fill in loop invariants here
    {
        let old_index = index;
        let old_sum = sum_neg;
        if (arr[index] < 0) {
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;

        assert(arr@.subrange(0, index as int).drop_last().len() == (index - 1) as int) by {
            lemma_len_drop_last(arr@.subrange(0, index as int));
        }

        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last()) by {
            assert(1 <= index as int <= arr@.len());
            lemma_subrange_drop_last_eq(arr@, index as int);
        }

        assert(sum_negative_to(arr@.subrange(0, index as int))
            == sum_negative_to(arr@.subrange(0, old_index as int))
                + if arr[old_index as int] < 0 { arr[old_index as int] as int } else { 0int }) by {
            lemma_sum_negative_to_step(arr@, index as int);
        }

        if arr[old_index] < 0 {
            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }
    }

    assert(index == arr.len());
    assert(arr@.subrange(0, index as int) == arr@);

    sum_neg
}

}