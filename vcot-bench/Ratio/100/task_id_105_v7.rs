use vstd::prelude::*;

fn main() {
}

verus! {

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            (1 as int)
        } else {
            (0 as int)
        }
    }
}

// Complete the lemma function below
proof fn lemma_subrange_drop_last_equiv<A>(s: Seq<A>, i: int)
   

// Complete the lemma function below
proof fn lemma_count_boolean_unfold_nonempty(s: Seq<bool>)
   

// Complete the lemma function below
proof fn lemma_subrange_add1_is_drop_last_plus_last(s: Seq<bool>, i: int)
   

// Complete the lemma function below
proof fn lemma_subrange_len_when_in_bounds_bool(s: Seq<bool>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;

    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    // Fill in a block of assertions here to complete the proof
    counter
}

}