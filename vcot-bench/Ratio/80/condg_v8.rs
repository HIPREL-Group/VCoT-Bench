use vstd::prelude::*;
fn main() {}
verus! {

// Complete the lemma function below
proof fn lemma_update_preserves_prefix_ones(old_a: Seq<i32>, i: int)
   

// Complete the lemma function below
proof fn lemma_seq_update_preserves_prefix(s: Seq<i32>, i: int, a: i32, bound: int)
   

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
        // Fill in loop invariants here
    {
        a.set(i, 1);
        // Fill in a block of assertions here to complete the proof
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
        proof {
            assert(sum[0] == i);
        }
    }

    i = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof
        if (sum[0] == N) {
            let temp = a[i];
            a.set(i, temp - 1);
            // Fill in a block of assertions here to complete the proof
        } else {
            let temp = a[i];
            a.set(i, temp + 1);
        }
        i = i + 1;
    }
}
}