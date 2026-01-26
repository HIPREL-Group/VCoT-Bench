use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_min_preserved_or_updated(
    old_min: i32,
    new_min: i32,
    x: i32,
)
   

// Complete the lemma function below
proof fn lemma_forall_extend_min(
    nums: &Vec<i32>,
    idx: int,
    old_min: i32,
    new_min: i32
)
   

// Complete the lemma function below
proof fn lemma_exists_extend_min(
    nums: &Vec<i32>,
    idx: int,
    old_min: i32,
    new_min: i32
)
   

#[verifier::exec_allows_no_decreases_clause]
fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    requires
        nums.len() > 0,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
{
    let mut min = nums[0];
    let mut index = 1;

    while index < nums.len()
        // Fill in loop invariants here
    {
        let old_min = min;

        if nums[index] < min {
            min = nums[index];
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    min
}

}