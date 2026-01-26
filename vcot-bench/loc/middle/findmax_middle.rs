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

    proof {
        assert(forall |k: int| 0 <= k < i ==> nums@[k] <= max) by {
            assert forall |k: int| 0 <= k < i implies nums@[k] <= max by {
                assert(k == 0);
                assert(nums@[0] == max);
            }
        }
        assert(exists |k: int| 0 <= k < i && nums@[k] == max);
    }

    while i < nums.len()
    // Fill in loop invariants here
    {
        if nums[i] > max {
            max = nums[i];
            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        i += 1;
    }

    proof {
        assert(i == nums.len());
        assert(forall |k: int| 0 <= k < nums@.len() ==> nums@[k] <= max) by {
            assert forall |k: int| 0 <= k < nums@.len() implies nums@[k] <= max by {
                assert(nums@[k] <= max);
            }
        }
        assert(exists |k: int| 0 <= k < nums@.len() && nums@[k] == max) by {
            let w = choose |k: int| 0 <= k < i && nums@[k] == max;
            assert(0 <= w && w < i && nums@[w] == max);
        }
    }

    max
}
}