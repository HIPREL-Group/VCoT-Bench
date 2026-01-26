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
        // Fill in loop invariants here
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
        // Fill in loop invariants here
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