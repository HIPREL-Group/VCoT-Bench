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
    

proof fn lemma_seq_push_to_set_insert<T>(s: Seq<T>, val: T)
ensures
    s.push(val).to_set() === s.to_set().insert(val),
{
    seq_to_set_equal_rec(s.push(val));
    assert(s =~= s.push(val).drop_last());
    seq_to_set_equal_rec(s);

    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val)));
    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val).drop_last()).insert(val));

    assert(s.push(val).drop_last() =~= s);
    assert(seq_to_set_rec(s.push(val).drop_last()) == seq_to_set_rec(s));
    assert(seq_to_set_rec(s.push(val)) == seq_to_set_rec(s).insert(val));

    assert(s.push(val).to_set() === s.to_set().insert(val));

    assert(s.push(val).to_set() =~= s.to_set().insert(val));
}

// Complete the lemma function below
proof fn lemma_set_insert_idempotent_if_contains(s: Set<i32>, v: i32)
   

// Complete the lemma function below
proof fn lemma_set_contains_of_insert(s: Set<i32>, v: i32, x: i32)
    

proof fn lemma_seq_to_set_insert_membership(s: Seq<i32>, v: i32, x: i32)
    ensures
        s.push(v).to_set().contains(x) <==> (x == v || s.to_set().contains(x))
{
    lemma_seq_push_to_set_insert(s, v);
    lemma_set_contains_of_insert(s.to_set(), v, x);
}

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
        // Fill in loop invariants here
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

        // Fill in a block of assertions here to complete the proof

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