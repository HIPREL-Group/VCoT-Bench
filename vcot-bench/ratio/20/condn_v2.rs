use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_forall_extend_by_one(a: &Vec<i32>, i_old: usize, N: i32)
    requires
        a.len() == N,
        i_old < N as usize,
        forall |k:int| 0 <= k < i_old ==> a[k] <= N,
        a[(i_old as int)] <= N,
        N > 0,
    ensures
        forall |k:int| 0 <= k < i_old + 1 ==> a[k] <= N,
{
    assert(forall |k:int| 0 <= k < i_old + 1 ==> a[k] <= N) by {
        assert forall |k:int| 0 <= k < i_old + 1 implies a[k] <= N by {
            if k < i_old {
                assert(a[k] <= N);
            } else {
                assert(a[(i_old as int)] <= N);
                assert(a[k] <= N);
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, N: i32, m: i32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] <= N,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            a.len() == N,
    {
        a.set(i, m);
        i = i + 1;

        // Fill in a block of assertions here to complete the proof
    }

    i = 0;
    while (i < N as usize)
        invariant
            forall |k:int| 0 <= k < i ==> a[k] <= N,
            a.len() == N,
    {
        if (a[i] < N) {
            proof {
                assert(a[(i as int)] < N);
                assert(a[(i as int)] <= N);
            }
            let temp = a[i];
            a.set(i, temp);
            proof {
                assert(a[(i as int)] == temp);
                assert(a[(i as int)] <= N);
            }
        } else {
            proof {
                assert(!(a[(i as int)] < N));
                assert(a[(i as int)] >= N);
            }
            a.set(i, N);
            proof {
                assert(a[(i as int)] == N);
                assert(a[(i as int)] <= N);
            }
        }

        // Fill in a block of assertions here to complete the proof

        i = i + 1;

        // Fill in a block of assertions here to complete the proof
    }

    proof {
        assert(forall |k:int| 0 <= k < N ==> a[k] <= N) by {
            let i_final = i;
            assert(forall |k:int| 0 <= k < i_final ==> a[k] <= N);
        }
    }
}

}