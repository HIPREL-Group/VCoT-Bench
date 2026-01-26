use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_vec_set_preserves_prefix_eq_1(a_before: Seq<i32>, a_after: Seq<i32>, i: usize)
    requires
        a_before.len() == a_after.len(),
        i < a_before.len(),
        a_after[i as int] == 1,
        forall |k: int| 0 <= k < i ==> a_before[k] == 1,
        forall |k: int| 0 <= k < a_before.len() ==> (k != i as int ==> a_after[k] == a_before[k]),
    ensures
        forall |k: int| 0 <= k < i + 1 ==> a_after[k] == 1,
{
    assert(forall |k: int| 0 <= k < i + 1 ==> a_after[k] == 1) by {
        assert forall |k: int| 0 <= k < i + 1 implies a_after[k] == 1 by {
            if k < i {
                assert(a_before[k] == 1);
                assert(a_after[k] == a_before[k]);
                assert(a_after[k] == 1);
            } else {
                assert(k == i as int);
                assert(a_after[i as int] == 1);
            }
        }
    }
}

proof fn lemma_vec_set_preserves_split_forall_eq_1(
    a_before: Seq<i32>,
    a_after: Seq<i32>,
    i: usize,
    n: usize,
)
    requires
        a_before.len() == n,
        a_after.len() == n,
        i < n,
        forall |k: int| 0 <= k < i ==> a_before[k] == 3,
        forall |k: int| i <= k < n ==> a_before[k] == 1,
        a_after[i as int] == 3,
        forall |k: int| 0 <= k < n ==> (k != i as int ==> a_after[k] == a_before[k]),
    ensures
        forall |k: int| 0 <= k < i + 1 ==> a_after[k] == 3,
        forall |k: int| i + 1 <= k < n ==> a_after[k] == 1,
{
    assert(forall |k: int| 0 <= k < i + 1 ==> a_after[k] == 3) by {
        assert forall |k: int| 0 <= k < i + 1 implies a_after[k] == 3 by {
            if k < i {
                assert(a_before[k] == 3);
                assert(a_after[k] == a_before[k]);
                assert(a_after[k] == 3);
            } else {
                assert(k == i as int);
                assert(a_after[i as int] == 3);
            }
        }
    }

    assert(forall |k: int| i + 1 <= k < n ==> a_after[k] == 1) by {
        assert forall |k: int| i + 1 <= k < n implies a_after[k] == 1 by {
            assert(a_after[k] == a_before[k]);
            assert(a_before[k] == 1);
        }
    }
}

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

        assert forall |k: int| 0 <= k < a.len() implies (k != i as int ==> a_after[k] == a_before[k]) by {
            if k != i as int {
                assert(a_after[k] == a_before[k]);
            }
        }

        assert(forall |k: int| 0 <= k < i + 1 ==> a[k] == 1) by {
            lemma_vec_set_preserves_prefix_eq_1(a_before, a_after, i);
        };

        i = i + 1;
    }

    i = 0;
    while (i < N)
        invariant
            a.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] == 3,
            forall |k: int| i <= k < N ==> a[k] == 1,
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
        invariant
            i <= N,
            a.len() == N,
            forall |k: int| 0 <= k < N ==> a[k] == 3,
            sum.len() == 1,
            sum[0] == 3 * i,
            N < 1000,
    {
        if (a[i] == 3) {
            let temp = sum[0] + a[i];
            sum.set(0, temp);

            assert(sum[0] == 3 * (i + 1)) by {
                assert(sum[0] == temp);
                assert(temp == 3 * i + 3);
            }
        } else {
            let temp = sum[0] * a[i];
            sum.set(0, temp);
        }

        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof
}

}