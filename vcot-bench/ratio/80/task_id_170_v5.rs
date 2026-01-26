use vstd::prelude::*;

fn main() {
}

verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

proof fn lemma_sum_to_push_last(s: Seq<i64>)
    requires
        s.len() > 0,
    ensures
        sum_to(s) == sum_to(s.drop_last()) + s.last(),
{
}

// Complete the lemma function below
proof fn lemma_subrange_succ_drop_last(arr: Seq<i64>, start: int, index: int)
   

// Complete the lemma function below
proof fn lemma_seq_last_of_subrange_is_index(arr: Seq<i64>, start: int, index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;

    while index < _end
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof

        sum = sum + arr[index] as i128;
        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }
    sum
}

} // verus!