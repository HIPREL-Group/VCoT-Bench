#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_forall_extend_by_split(nums: &Vec<i32>, target: i32, i_old: usize)
    requires
        i_old < nums.len(),
        forall |k: int| 0 <= k < (i_old as int) ==> #[trigger] nums@[k] != target,
        nums@[i_old as int] != target,
    ensures
        forall |k: int| 0 <= k < ((i_old + 1) as int) ==> #[trigger] nums@[k] != target,
{
    assert(forall |k: int| 0 <= k < ((i_old + 1) as int) ==> #[trigger] nums@[k] != target) by {
        let k: int;
        if 0 <= k < ((i_old + 1) as int) {
            if k < (i_old as int) {
                assert(nums@[k] != target);
            } else {
                assert(k == (i_old as int));
                assert(nums@[k] == nums@[i_old as int]);
                assert(nums@[k] != target);
            }
        }
    };
}

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
    invariant
        forall |k: int| 0 <= k < i ==> #[trigger]nums@[k] != target,
        0 <= i <= nums@.len(),
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