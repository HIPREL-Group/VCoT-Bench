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

// Complete the lemma function below
proof fn lemma_len_drop_last(s: Seq<i64>)
   

// Complete the lemma function below
proof fn lemma_subrange_drop_last_eq(s: Seq<i64>, k: int)
   

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

        // Fill in a block of assertions here to complete the proof

        if arr[old_index] < 0 {
            // Fill in a block of assertions here to complete the proof
        } else {
            assert(sum_neg == old_sum);
            assert(sum_negative_to(arr@.subrange(0, index as int)) == sum_neg) by {
                assert(sum_negative_to(arr@.subrange(0, old_index as int)) == old_sum);
            }
        }
    }

    // Fill in a block of assertions here to complete the proof;

    sum_neg
}

}