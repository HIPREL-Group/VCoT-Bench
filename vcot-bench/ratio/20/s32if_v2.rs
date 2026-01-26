use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_extend_by_one(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        forall |k:int| 0 <= k < (i as int) ==> a[k] == 1,
        a[(i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < (i + 1) as int ==> a[k] == 1,
{
    assert forall |k:int| 0 <= k < (i + 1) as int implies a[k] == 1 by {
        if k < (i as int) {
            assert(a[k] == 1);
        } else {
            assert(k == (i as int));
            assert(a[(i as int)] == 1);
        }
    }
}

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_4(a: &Vec<i32>, i: usize)
   

proof fn lemma_forall_suffix_shift_by_one(a: &Vec<i32>, i: usize, n: usize)
    requires
        i < n,
        forall |k:int| i as int <= k < n as int ==> a[k] == 1,
    ensures
        forall |k:int| (i + 1) as int <= k < n as int ==> a[k] == 1,
{
    assert forall |k:int| (i + 1) as int <= k && k < n as int implies a[k] == 1 by {
        assert(a[k] == 1);
    }
}

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N)
        invariant
            forall |k:int| 0<=k <i ==> a[k] == 1,
            a.len() == N,
        decreases
            N - i,
    {
        a.set(i, 1);
        // Fill in a block of assertions here to complete the proof
        i = i + 1;
    }

    i = 0;
    while (i < N)
        invariant
            forall |k:int| 0<=k <i ==> a[k] == 4,
            forall |k:int| i<=k <N ==> a[k] == 1,
            a.len() == N,
        decreases
            N - i,
    {
        proof { lemma_forall_suffix_shift_by_one(a, i, N); }

        if (a[i] == 1) {
            let temp = a[i];
            a.set(i, temp + 3);
        } else {
            let temp = a[i];
            a.set(i, temp - 1);
        }

        proof { lemma_forall_extend_by_one_4(a, i); }
        i = i + 1;

        assert(forall |k:int| i<=k <N ==> a[k] == 1);
    }

    i = 0;
    while (i < N)
        invariant
            i <= N,
            forall |k:int| 0<=k <N ==> a[k] == 4,
            a.len() == N,
            sum[0] == 4 * i,
            sum.len() == 1,
            N < 1000,
        decreases
            N - i,
    {
        if (a[i] == 4) {
            let temp = sum[0] + a[i];
            sum.set(0, temp);
        } else {
            let temp = sum[0] * a[i];
            sum.set(0, temp);
        }

        i = i + 1;
    }

    assert(sum[0] == 4 * N);
}
}