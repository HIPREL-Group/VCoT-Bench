use vstd::prelude::*;
fn main() {}
verus! {

// Complete the lemma function below
proof fn lemma_forall_extend_by_set_i32(v: &Vec<i32>, i: usize)
   

proof fn lemma_forall_len_eq_and_bound_transfer_i32(v: &Vec<i32>, n: i32, i: usize)
    requires
        v.len() == n,
        i < n as usize,
        n >= 0,
    ensures
        i < v.len(),
{
    assert(i < v.len());
}

proof fn lemma_finish_sum_is_3n(sum0: i32, i: usize, n: i32)
    requires
        n > 0,
        i == n as usize,
        sum0 == i + 2 * n,
        n < 1000,
    ensures
        sum0 == 3 * n,
{
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(
    a: &mut Vec<i32>,
    b: &mut Vec<i32>,
    c: &mut Vec<i32>,
    sum: &mut Vec<i32>,
    N: i32,
)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);

    let mut i: usize = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof
        a.set(i, 1);

        proof {
            assert(i < a.len()) by {
                lemma_forall_len_eq_and_bound_transfer_i32(a, N, i);
            }
            assert(a[(i as int)] == 1);
            lemma_forall_extend_by_set_i32(a, i);
        }

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        let temp = sum[0] + a[i];
        sum.set(0, temp);

        assert(sum[0] == i + 1);

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof
        b.set(i, 1);

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        invariant
            i <= N,
            sum.len() == 1,
            sum[0] == i + N,
            b.len() == N,
            forall |j: int| 0 <= j < N ==> b[j] == 1,
            N < 1000,
    {
        // Fill in a block of assertions here to complete the proof;

        let temp = sum[0] + b[i];
        sum.set(0, temp);

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        invariant
            forall |j: int| 0 <= j < i ==> c[j] == 1,
            c.len() == N,
    {
        // Fill in a block of assertions here to complete the proof
        c.set(i, 1);

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        // Fill in loop invariants here
    {
        // Fill in a block of assertions here to complete the proof;

        let temp = sum[0] + c[i];
        sum.set(0, temp);

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    assert(sum[0] == 3 * N) by {
        assert(sum[0] == i + 2 * N);
        lemma_finish_sum_is_3n(sum[0], i, N);
    };
    assert(sum[0] <= 3 * N);
}

}