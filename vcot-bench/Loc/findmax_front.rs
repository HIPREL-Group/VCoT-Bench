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
    invariant
        1 <= i <= nums.len(),
        forall |k: int| 0 <= k < i ==> nums@[k] <= max,
        exists |k: int| 0 <= k < i && nums@[k] == max,
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
            proof {
                assert(exists |k: int| 0 <= k < i + 1 && nums@[k] == max) by {
                    let w = choose |k: int| 0 <= k < i && nums@[k] == max;
                    assert(0 <= w && w < i && nums@[w] == max);
                }

                assert forall |k: int| 0 <= k < i + 1 implies nums@[k] <= max by {
                    if k < i {
                        assert(nums@[k] <= max);
                    } else {
                        assert(k == i);
                        assert(nums@[k] == nums[(i as int)]);
                        assert(nums[(i as int)] <= max);
                    }
                }
            }
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