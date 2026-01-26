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

        assert(a_after[i as int] == 3);

        assert forall |k: int| 0 <= k < N implies (k != i as int ==> a_after[k] == a_before[k]) by {
            if k != i as int {
                assert(a_after[k] == a_before[k]);
            }
        }

        assert(forall |k: int| 0 <= k < i + 1 ==> a[k] == 3) by {
            lemma_vec_set_preserves_split_forall_eq_1(a_before, a_after, i, N);
        }

        assert(forall |k: int| i + 1 <= k < N ==> a[k] == 1) by {
            lemma_vec_set_preserves_split_forall_eq_1(a_before, a_after, i, N);
        }

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

    assert(i == N) by {
        assert(!(i < N));
    }
    assert(sum[0] == 3 * N) by {
        assert(sum[0] == 3 * i);
        assert(i == N);
    }
}

}