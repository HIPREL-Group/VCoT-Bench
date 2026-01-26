use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_vec_set_preserves_prefix_eq_1(a_before: Seq<i32>, a_after: Seq<i32>, i: usize)
   

// Complete the lemma function below
proof fn lemma_vec_set_preserves_split_forall_eq_1(
    a_before: Seq<i32>,
    a_after: Seq<i32>,
    i: usize,
    n: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while (i < N)
        // Fill in loop invariants here
    {
        let ghost a_before = a@;

        a.set(i, 1);

        let ghost a_after = a@;

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    i = 0;
    while (i < N)
        // Fill in loop invariants here
    {
        let ghost a_before = a@;

        if (a[i] == 1) {
            let temp = a[i];
            a.set(i, temp + 2);
        } else {
            let temp = a[i];
            a.set(i, temp - 1);
        }

        let ghost a_after = a@;

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }

    i = 0;
    while (i < N)
        // Fill in loop invariants here
    {
        if (a[i] == 3) {
            let temp = sum[0] + a[i];
            sum.set(0, temp);

            // Fill in a block of assertions here to complete the proof
        } else {
            let temp = sum[0] * a[i];
            sum.set(0, temp);
        }

        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof
}

}