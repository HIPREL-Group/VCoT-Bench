#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

fn main() {
}

verus! {

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

// Complete the lemma function below
proof fn lemma_subrange_drop_last<T>(s: Seq<T>, j: int, k: int)
   

// Complete the lemma function below
proof fn lemma_subrange_push_last_i32(s: Seq<i32>, k: int)
   

// Complete the lemma function below
proof fn lemma_max_rcur_push_last_i32(s: Seq<i32>, k: int)
   

// Complete the lemma function below
proof fn lemma_min_rcur_push_last_i32(s: Seq<i32>, k: int)
   

// Complete the lemma function below
proof fn lemma_max_rcur_update_step(arr: Seq<i32>, k: int, old_max: i32)
   

// Complete the lemma function below
proof fn lemma_min_rcur_update_step(arr: Seq<i32>, k: int, old_min: i32)
   

#[verifier::exec_allows_no_decreases_clause]
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut min_val = arr[0];
    let mut max_val = arr[0];
    let mut index = 1;
    
    // Fill in a block of assertions here to complete the proof

    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] <= min_val) {
            min_val = arr[index];
        } else if (arr[index] > max_val) {
            max_val = arr[index];
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    // Fill in a block of assertions here to complete the proof
    max_val + min_val
}

} // verus!