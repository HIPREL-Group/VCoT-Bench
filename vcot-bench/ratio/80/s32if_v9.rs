use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_extend_by_one(a: &Vec<i32>, i: usize)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_4(a: &Vec<i32>, i: usize)
   

// Complete the lemma function below
proof fn lemma_forall_suffix_shift_by_one(a: &Vec<i32>, i: usize, n: usize)
   

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
        proof { lemma_forall_extend_by_one(a, i); }
        i = i + 1;
    }

    i = 0;
    while (i < N)
        // Fill in loop invariants here
        decreases
            N - i,
    {
        // Fill in a block of assertions here to complete the proof

        if (a[i] == 1) {
            let temp = a[i];
            a.set(i, temp + 3);
        } else {
            let temp = a[i];
            a.set(i, temp - 1);
        }

        // Fill in a block of assertions here to complete the proof
        i = i + 1;

        // Fill in a block of assertions here to complete the proof;
    }

    i = 0;
    while (i < N)
        // Fill in loop invariants here
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

    // Fill in a block of assertions here to complete the proof;
}
}