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
   

proof fn lemma_forall_extend_min(
    nums: &Vec<i32>,
    idx: int,
    old_min: i32,
    new_min: i32
)
    requires
        0 <= idx,
        idx < nums.len(),
        forall|k: int| 0 <= k < idx ==> old_min <= nums[k],
        new_min == old_min || new_min == nums[idx],
        nums[idx] < old_min ==> new_min == nums[idx],
        !(nums[idx] < old_min) ==> new_min == old_min,
    ensures
        forall|k: int| 0 <= k < idx + 1 ==> new_min <= nums[k],
{
    let x = nums[idx];
    lemma_min_preserved_or_updated(old_min, new_min, x);

    assert forall|k: int| 0 <= k < idx + 1 implies new_min <= nums[k] by {
        if k < idx {
            assert(old_min <= nums[k]);
        } else {
            assert(new_min <= nums[idx]);
        }
    };
}

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