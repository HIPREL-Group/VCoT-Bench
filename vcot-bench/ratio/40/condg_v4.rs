use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_update_preserves_prefix_ones(old_a: Seq<i32>, i: int)
    requires
        0 <= i < old_a.len(),
        forall|k: int| 0 <= k < i ==> old_a[k] == 1,
    ensures
        forall|k: int| 0 <= k < i + 1 ==> old_a.update(i, 1)[k] == 1,
{
    assert forall|k: int| 0 <= k < i + 1 implies old_a.update(i, 1)[k] == 1 by {
        if k < i {
            assert(old_a[k] == 1);
        } else {
            assert(old_a.update(i, 1)[k] == 1);
        }
    };
}

proof fn lemma_seq_update_preserves_prefix(s: Seq<i32>, i: int, a: i32, bound: int)
    requires
        0 <= i < s.len(),
        i < bound,
        bound <= s.len(),
        forall|k: int| 0 <= k < bound ==> s[k] == 1,
        a == 1,
    ensures
        forall|k: int| 0 <= k < bound ==> s.update(i, a)[k] == 1,
{
    assert forall|k: int| 0 <= k < bound implies s.update(i, a)[k] == 1 by {
        if k == i {
            if a == 1 {
                assert(s.update(i, a)[k] == 1);
            } else {
                assert(s[k] == 1);
                assert(false);
            }
        } else {
            assert(s[k] == 1);
        }
    };
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == 0,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            forall |k:int| 0 <= k < i ==> a[k] == 1,
            a.len() == N,
    {
        a.set(i, 1);
        proof {
            let ii: int = i as int;
            lemma_update_preserves_prefix_ones(a@, ii);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
            a.len() == N,
            sum[0] == i,
            sum.len() == 1,
    {
        let temp = sum[0];
        sum.set(0, temp + a[i]);
        // Fill in a block of assertions here to complete the proof
        i = i + 1;
        // Fill in a block of assertions here to complete the proof
    }

    i = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof
        if (sum[0] == N) {
            let temp = a[i];
            a.set(i, temp - 1);
            proof {
                assert forall |k:int| 0 <= k < (i as int) + 1 implies a[k] == 0 by {
                    if k < (i as int) {
                        assert(a[k] == 0);
                    } else {
                        assert(k == (i as int));
                        assert(a[k] == 0);
                    }
                };

                assert forall |k:int| (i as int) + 1 <= k < N implies a[k] == 1 by {
                    assert(a[k] == 1);
                };
            }
        } else {
            let temp = a[i];
            a.set(i, temp + 1);
        }
        i = i + 1;
    }
}
}