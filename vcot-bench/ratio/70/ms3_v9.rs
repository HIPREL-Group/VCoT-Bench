use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_i32_mod3_in_range(i: int)
    

// Complete the lemma function below
proof fn lemma_set_extends_prefix_range3(a: &Vec<i32>, i: usize)
   

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

        assert(tmp == 0 || tmp == 1 || tmp == 2) by {
            let ii: int = i as int;
            lemma_i32_mod3_in_range(ii);
            assert((ii % 3) == 0 || (ii % 3) == 1 || (ii % 3) == 2);
            assert(tmp == 0 || tmp == 1 || tmp == 2);
        }

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

            // Fill in a block of assertions here to complete the proof
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