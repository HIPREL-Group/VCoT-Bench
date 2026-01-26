#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend_by_split(nums: &Vec<i32>, target: i32, i_old: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums@.len() < 0x8000_0000,
ensures
    ret < nums@.len(),
    ret >=0 ==> nums@[ret as int] == target,
    ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i]!= target,
    ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target,
{
    let mut i = 0;

    while i < nums.len()
    // Fill in loop invariants here
    ensures
        0 <= i < nums@.len() ==> (#[trigger]nums@[i as int]) == target,
    {
        if nums[i] == target {
            break;
        }

        if i < nums.len() {
            proof {
                lemma_forall_extend_by_split(&nums, target, i);
            }
        }

        i = i + 1;
    }

    if i == nums.len() {
        -1
    } else {
        i as i32
    }
}
}