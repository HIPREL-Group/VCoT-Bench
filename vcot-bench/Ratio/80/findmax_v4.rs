#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn find_max(nums: Vec<i32>) -> (ret:i32)
requires
    nums.len() > 0,
ensures
    forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
    exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    let mut max = nums[0];
    let mut i = 1;

    // Fill in a block of assertions here to complete the proof

    while i < nums.len()
    // Fill in loop invariants here
    {
        if nums[i] > max {
            max = nums[i];
            proof {
                assert(exists |k: int| 0 <= k < i + 1 && nums@[k] == max);

                assert forall |k: int| 0 <= k < i + 1 implies nums@[k] <= max by {
                    if k < i {
                        assert(nums@[k] < max);
                    } else {
                        assert(k == i);
                    }
                }
            }
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof

    max
}
}