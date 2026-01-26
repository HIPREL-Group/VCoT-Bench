use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }


    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
    }

    // Complete the lemma function below
proof fn lemma_is_reorder_of_identity_u32(s: Seq<u32>)
        

    proof fn lemma_is_reorder_of_swap_update_u32(
        r1: Seq<int>,
        p: Seq<u32>,
        s: Seq<u32>,
        j: int,
    )
        requires
            is_reorder_of(r1, p, s),
            0 <= j - 1,
            j < p.len(),
            p.len() == s.len(),
            r1.len() == p.len(),
        ensures
            is_reorder_of(r1.update(j - 1, r1[j]).update(j, r1[j - 1]),
                p.update(j - 1, p[j]).update(j, p[j - 1]),
                s),
    {
        let r2 = r1.update(j - 1, r1[j]).update(j, r1[j - 1]);
        let p2 = p.update(j - 1, p[j]).update(j, p[j - 1]);

        assert(r2.len() == r1.len());
        assert(p2.len() == p.len());
        assert(r2.len() == s.len()) by {
            assert(r2.len() == r1.len());
        }

        assert(forall|i: int| 0 <= i < r2.len() ==> 0 <= #[trigger] r2[i] < r2.len());

        assert(forall|i: int, k: int| 0 <= i < k < r2.len() ==> r2[i] != r2[k]);

        let mapped2 = r2.map_values(|idx: int| s[idx]);
        assert(p2 =~= mapped2);

        assert(is_reorder_of(r2, p2, s));
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        proof {
            let r = Seq::new(nums@.len(), |i: int| i);
            lemma_is_reorder_of_identity_u32(nums@);
            assert(is_reorder_of(r, nums@, nums@));

            assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)) by {
                assert(old(nums)@ == nums@);
                assert(is_reorder_of(r, nums@, old(nums)@));
            }
        }
        let n = nums.len();
        if n == 0 {
            return;
        }
        for i in 1..n
            // Fill in loop invariants here
        {
            let mut j = i;
            while j != 0
                // Fill in loop invariants here
            {
                if nums[j - 1] > nums[j] {
                    // Fill in a block of assertions here to complete the proof
                    let temp1 = nums[j];
                    let temp2 = nums[j - 1];
                    nums.set(j - 1, temp1);
                    nums.set(j, temp2);
                }
                j -= 1;
            }
        }
    }
}