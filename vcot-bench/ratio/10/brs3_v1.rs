use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_extend_prefix_property_after_set(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        forall |k: int| 0 <= k < i ==> a[k] == 3 || a[k] == 0,
        a[(i as int)] == 3 || a[(i as int)] == 0,
    ensures
        forall |k: int| 0 <= k < i + 1 ==> a[k] == 3 || a[k] == 0,
{
    assert forall |k: int| 0 <= k < i + 1 implies a[k] == 3 || a[k] == 0 by {
        if k < i {
            assert(a[k] == 3 || a[k] == 0);
        } else {
            assert(k == (i as int));
            assert(a[k] == 3 || a[k] == 0);
        }
    }
}

proof fn lemma_sum_step(sum_before: int, a_i: int, i: usize)
    requires
        i > 0,
        sum_before <= 3 * (i as int),
        a_i == 3 || a_i == 0,
    ensures
        sum_before + a_i <= 3 * ((i + 1) as int),
{
    if a_i == 0 {
        assert(sum_before + a_i <= 3 * ((i + 1) as int));
    } else {
        assert(a_i == 3);
        assert(sum_before + a_i <= 3 * ((i + 1) as int));
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            forall |k: int| 0<= k < i ==> a[k] == 3 || a[k] == 0,
            a.len() == N,
    {
        if (i % 3 == 0) {
            a.set(i, 3);
            // Fill in a block of assertions here to complete the proof
        } else {
            a.set(i, 0);
            // Fill in a block of assertions here to complete the proof
        }
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N as usize,
            forall |k: int| 0<= k < N ==> a[k] == 3 || a[k] == 0,
            a.len() == N,
            sum.len() == 1,
            i>0 ==> sum[0] <= 3 * (i as int),
            N < 1000,
    {
        if (i == 0) {
            sum.set(0, 0);
            assert(sum[0] <= 3 * ((i as int) + 1));
        } else {
            let temp = sum[0];
            proof {
                assert(sum[0] <= 3 * (i as int));
                lemma_sum_step(temp as int, a[(i as int)] as int, i);
            }
            sum.set(0, temp + a[i]);
            proof {
                assert(sum[0] <= 3 * ((i + 1) as int));
            }
        }
        i = i + 1;
        proof {
            assert(i > 0 ==> sum[0] <= 3 * (i as int));
        }
    }

    proof {
        assert(sum[0] <= 3 * N);
    }
}
}