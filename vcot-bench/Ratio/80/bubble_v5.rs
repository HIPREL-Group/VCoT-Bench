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

    proof fn lemma_is_reorder_of_identity_u32(s: Seq<u32>)
        ensures
            is_reorder_of(Seq::new(s.len(), |i: int| i), s, s),
    {
        let r = Seq::new(s.len(), |i: int| i);

        assert(r.len() == s.len());

        assert(forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len());

        assert(forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]);

        let mapped = r.map_values(|i: int| s[i]);

        assert(s =~= mapped) by {
            assert(forall|k: int| 0 <= k < s.len() ==> s[k] == mapped[k]);
        }

        assert(is_reorder_of(r, s, s));
    }

    // Complete the lemma function below
proof fn lemma_is_reorder_of_swap_update_u32(
        r1: Seq<int>,
        p: Seq<u32>,
        s: Seq<u32>,
        j: int,
    )
       

    #[verifier::exec_allows_no_decreases_clause]
    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        // Fill in a block of assertions here to complete the proof
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