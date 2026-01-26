use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_forall_extend_to_next(prev_i: usize, a: &Vec<i32>)
    requires
        forall |k: int| 0 <= k < prev_i ==> a[k] == 1,
        a[prev_i as int] == 1,
    ensures
        forall |k: int| 0 <= k < prev_i + 1 ==> a[k] == 1,
{
    assert(forall |k: int| 0 <= k < prev_i + 1 ==> a[k] == 1) by {
        assert forall |k: int| 0 <= k < prev_i + 1 implies a[k] == 1 by {
            if k < prev_i as int {
                assert(a[k] == 1);
            } else {
                assert(a[prev_i as int] == 1);
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
    {
        if (i % 1 == 0) {
            a.set(i, 1);
        } else {
            a.set(i, 0);
        }

        let i_prev = i;
        i = i + 1;

        proof {
            lemma_forall_extend_to_next(i_prev, a);
            assert(forall |k:int| 0 <= k < i ==> a[k] == 1);
        }
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            i > 0 ==> sum[0] <= i,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            let current_sum = sum[0];
            sum.set(0, current_sum + a[i]);
        }

        let i_old = i;
        let sum_old = sum[0];
        i = i + 1;

        proof {
            if i_old == 0 {
                assert(sum[0] <= i as int);
            } else {
                assert(sum[0] <= i as int);
            }

            assert(i > 0 ==> sum[0] <= i);
        }
    }

    proof {
        assert(sum[0] <= N) by {
            assert(i > 0 ==> sum[0] <= i);
            assert(i == N as usize);
            assert(sum[0] <= i);
            assert(sum[0] <= N);
        }
    }
}
}