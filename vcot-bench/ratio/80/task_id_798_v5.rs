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

// Complete the lemma function below
proof fn lemma_sum_to_step_by_subrange(arr: Seq<i64>, index: int)
   

// Complete the lemma function below
proof fn lemma_sum_loop_step(arr: Seq<i64>, index: int, sum_prev: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        sum = sum + arr[index] as i128;
        index += 1;

        assert(sum == sum_to(arr@.subrange(0, index as int))) by {
            assert(index >= 1);
            assert(sum_to(arr@.subrange(0, index as int))
                == sum_to(arr@.subrange(0, (index - 1) as int)) + arr@[(index - 1) as int]) by {
                lemma_sum_to_step_by_subrange(arr@, (index - 1) as int);
            };
        };
    }
    // Fill in a block of assertions here to complete the proof;
    sum
}

} // verus!