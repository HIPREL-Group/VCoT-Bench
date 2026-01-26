use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_i32_mod3_in_range(i: int)
    

proof fn lemma_set_extends_prefix_range3(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        forall|k: int| 0 <= k < i as int ==> a[k] == 0 || a[k] == 1 || a[k] == 2,
        a[i as int] == 0 || a[i as int] == 1 || a[i as int] == 2,
    ensures
        forall|k: int| 0 <= k < (i + 1) as int ==> a[k] == 0 || a[k] == 1 || a[k] == 2,
{
    assert forall|k: int| 0 <= k < (i + 1) as int implies a[k] == 0 || a[k] == 1 || a[k] == 2 by {
        if k < i as int {
            assert(a[k] == 0 || a[k] == 1 || a[k] == 2);
        } else {
            assert(a[k] == 0 || a[k] == 1 || a[k] == 2);
        }
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
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            forall|k: int| 0 <= k < i ==> a[k] == 0 || a[k] == 1 || a[k] == 2,
            a.len() == N,
    {
        let tmp = (i % 3) as i32;

        // Fill in a block of assertions here to complete the proof

        a.set(i, tmp);

        // Fill in a block of assertions here to complete the proof

        i = i + 1;

        // Fill in a block of assertions here to complete the proof
    }

    i = 0;

    while (i < N as usize)
        invariant
            i <= N,
            forall|k: int| 0 <= k < N ==> a[k] == 0 || a[k] == 1 || a[k] == 2,
            a.len() == N,
            sum.len() == 1,
            i > 0 ==> sum[0] <= 2 * i,
            N < 1000,
    {
        if (i == 0) {
            sum.set(0, 0);

            assert(sum[0] <= 2 * (i + 1)) by {
                assert(sum[0] == 0);
                assert(0 <= 2 * (i + 1));
            }
        } else {
            let ai = a[i];
            // Fill in a block of assertions here to complete the proof

            let sum_old = sum[0];
            // Fill in a block of assertions here to complete the proof

            let temp = sum_old + a[i];
            sum.set(0, temp);

            // Fill in a block of assertions here to complete the proof
        }
        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof
}

}