use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_forall_extend_by_one(a: &Vec<i32>, i_old: usize, N: i32)
   

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
        // Fill in loop invariants here
    {
        a.set(i, m);
        i = i + 1;

        // Fill in a block of assertions here to complete the proof
    }

    i = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        if (a[i] < N) {
            proof {
                assert(a[(i as int)] < N);
                assert(a[(i as int)] <= N);
            }
            let temp = a[i];
            a.set(i, temp);
            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
            a.set(i, N);
            // Fill in a block of assertions here to complete the proof
        }

        proof {
            let i_old = i;
            assert(forall |k:int| 0 <= k < i_old ==> a[k] <= N);
            lemma_forall_extend_by_one(a, i_old, N);
        }

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