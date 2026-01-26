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

proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        assert(forall |a| #[trigger] seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }

        assert(seq =~= (seq.drop_last().push(seq.last())));

        assert forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            let dl = seq.drop_last();
            let last = seq.last();
            assert(seq_to_set_rec(seq) == seq_to_set_rec(dl).insert(last));

            if dl.contains(a) {
                assert(seq_to_set_rec(dl).contains(a));
                assert(seq_to_set_rec(seq).contains(a));
                assert(seq.contains(a));
            } else {
                if a == last {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(dl).contains(a));
                    assert(!seq_to_set_rec(seq).contains(a));
                    assert(!seq.contains(a));
                }
            }
        }
    }
}

proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures seq.to_set() == seq_to_set_rec(seq)
{
    assert(forall |n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }

    assert(forall |n: A| #[trigger] seq.to_set().contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        assert forall |n: A| #[trigger] seq.to_set().contains(n) <==> seq_to_set_rec(seq).contains(n) by {
            assert(seq.to_set().contains(n) <==> seq.contains(n));
            assert(seq.contains(n) <==> seq_to_set_rec(seq).contains(n));
        }
    }

    assert(seq.to_set() =~= seq_to_set_rec(seq));
}

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

proof fn lemma_set_insert_idempotent_if_contains(s: Set<i32>, v: i32)
    requires
        s.contains(v),
    ensures
        s =~= s.insert(v),
{
    assert forall |x: i32| #[trigger] s.contains(x) <==> s.insert(v).contains(x) by {
        if x == v {
            assert(s.contains(x));
            assert(s.insert(v).contains(x));
        } else {
            assert(s.contains(x) <==> s.insert(v).contains(x));
        }
    }
}

proof fn lemma_set_contains_of_insert(s: Set<i32>, v: i32, x: i32)
    ensures
        s.insert(v).contains(x) <==> (x == v || s.contains(x))
{
    if x == v {
        assert(s.insert(v).contains(x));
    } else {
        assert(s.insert(v).contains(x) <==> s.contains(x));
        assert(x == v || s.contains(x) <==> s.contains(x));
    }
}

proof fn lemma_seq_to_set_insert_membership(s: Seq<i32>, v: i32, x: i32)
    ensures
        s.push(v).to_set().contains(x) <==> (x == v || s.to_set().contains(x))
{
    lemma_seq_push_to_set_insert(s, v);
    lemma_set_contains_of_insert(s.to_set(), v, x);
}

proof fn lemma_subrange_push_last(nums: Seq<i32>, i: int)
    requires
        0 <= i < nums.len(),
    ensures
        nums.subrange(0, i + 1) =~= nums.subrange(0, i).push(nums[i])
{
    let val = nums[i];
    assert(nums.subrange(0, i + 1) =~= nums.subrange(0, i).push(val));
}

proof fn lemma_to_set_subrange_succ(nums: Seq<i32>, i: int)
    requires
        0 <= i < nums.len(),
    ensures
        nums.subrange(0, i + 1).to_set() =~= nums.subrange(0, i).to_set().insert(nums[i])
{
    let val = nums[i];
    lemma_seq_push_to_set_insert(nums.subrange(0, i), val);
    lemma_subrange_push_last(nums, i);
    assert(nums.subrange(0, i + 1).to_set() === nums.subrange(0, i).push(val).to_set());
    assert(nums.subrange(0, i).push(val).to_set() === nums.subrange(0, i).to_set().insert(val));
}

proof fn lemma_subrange_full_to_set<T>(s: Seq<T>)
    ensures
        s.subrange(0, s.len() as int) =~= s,
        s.subrange(0, s.len() as int).to_set() == s.to_set(),
{
    assert(s.subrange(0, s.len() as int) =~= s);
    assert(s.subrange(0, s.len() as int).to_set() == s.to_set()) by {
        assert forall |x: T| #[trigger] s.subrange(0, s.len() as int).to_set().contains(x)
            <==> s.to_set().contains(x) by {
            assert(s.subrange(0, s.len() as int).to_set().contains(x) <==> s.subrange(0, s.len() as int).contains(x));
            assert(s.to_set().contains(x) <==> s.contains(x));
            assert(s.subrange(0, s.len() as int).contains(x) <==> s.contains(x));
        }
        assert(s.subrange(0, s.len() as int).to_set() =~= s.to_set());
    }
}

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
    // Fill in a block of assertions here to complete the proof
    res
}
}