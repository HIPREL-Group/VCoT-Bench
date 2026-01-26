#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

// Complete the lemma function below
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    

// Complete the lemma function below
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    

// Complete the lemma function below
proof fn lemma_seq_push_to_set_insert<T>(s: Seq<T>, val: T)


// Complete the lemma function below
proof fn lemma_set_insert_idempotent_if_contains(s: Set<i32>, v: i32)
   

// Complete the lemma function below
proof fn lemma_set_contains_of_insert(s: Set<i32>, v: i32, x: i32)
    

// Complete the lemma function below
proof fn lemma_seq_to_set_insert_membership(s: Seq<i32>, v: i32, x: i32)
    

// Complete the lemma function below
proof fn lemma_subrange_push_last(nums: Seq<i32>, i: int)
   

// Complete the lemma function below
proof fn lemma_to_set_subrange_succ(nums: Seq<i32>, i: int)
   

// Complete the lemma function below
proof fn lemma_subrange_full_to_set<T>(s: Seq<T>)
    

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set() =~= (res@.to_set())
{
    let mut res = Vec::new();
    let mut i = 0;
    while i < nums.len()
    invariant
        0 <= i <= nums@.len(),
        nums@.subrange(0, i  as int).to_set() =~= (res@.to_set()),
        res@.no_duplicates(),
    decreases nums.len() - i
    {
        let mut found = false;
        let mut j = 0;

        while j < res.len()
        invariant_except_break
            !found
        invariant
            0 <= i < nums@.len(),
            0 <= j <= res@.len(),
            res@.no_duplicates(),
            nums@.subrange(0, i  as int).to_set() =~= (res@.to_set()),
            forall |k| 0 <= k < j ==> res@[k] != nums@[i as int],
        ensures
            0<= i < nums@.len(),
            0 <= j <= res@.len(),
            res@.no_duplicates(),
            nums@.subrange(0, i  as int).to_set() =~= (res@.to_set()),
            found ==> (j < res@.len() && res@[j as int] == nums@[i as int]),
            !found ==> forall |k| 0 <= k < j ==> res@[k] != nums@[i as int],
            !found ==> j == res@.len()
        decreases res.len() - j
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }

        proof {
            let val = nums@[i as int];

            lemma_subrange_push_last(nums@, i as int);
            lemma_to_set_subrange_succ(nums@, i as int);

            lemma_seq_push_to_set_insert(res@, val);

            if found {
                assert(res@.contains(val));
                assert(res@.to_set().contains(val));
                lemma_set_insert_idempotent_if_contains(res@.to_set(), val);
                assert(nums@.subrange(0, i as int + 1).to_set() =~= (res@.to_set()));
            }

            if !found {
                assert(forall |k| 0 <= k < res@.len() ==> res@[k] != val);
                assert(!res@.to_set().contains(val));
                assert(res@.to_set().insert(val).contains(val));
                assert(nums@.subrange(0, i as int + 1).to_set().contains(val));
            }
        }

        if !found {
            res.push(nums[i]);
        }

        i += 1;
    }
    proof {
        assert(nums@.subrange(0, i  as int) =~= (nums@));
        assert(i == nums.len());
        assert(nums@.subrange(0, nums@.len() as int) =~= nums@);

        assert(nums@.subrange(0, i as int).to_set() =~= res@.to_set());
        assert(nums@.to_set() =~= res@.to_set()) by {
            assert(nums@.subrange(0, i as int) == nums@.subrange(0, nums@.len() as int)) by {
                assert(i as int == nums@.len() as int);
            }
            lemma_subrange_full_to_set::<i32>(nums@);
            assert(nums@.subrange(0, nums@.len() as int).to_set() == nums@.to_set());
            assert(nums@.subrange(0, nums@.len() as int).to_set() =~= res@.to_set());
        }
    }
    res
}
}