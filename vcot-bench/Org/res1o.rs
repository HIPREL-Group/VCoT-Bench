use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_extend_prefix_set_to_one_a(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        forall |k:int| 0 <= k < i ==> a[k] == 1,
        a[(i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> a[k] == 1,
{
    assert forall |k:int| 0 <= k < i + 1 implies a[k] == 1 by {
        if 0 <= k < i {
            assert(a[k] == 1);
        } else {
            assert(k == i) by {
                assert(k < i + 1);
                assert(!(k < i));
                assert(k >= i);
            }
            assert(a[k] == a[(i as int)]);
            assert(a[(i as int)] == 1);
        }
    }
}

proof fn lemma_extend_prefix_set_to_one_b(b: &Vec<i32>, i: usize)
    requires
        i < b.len(),
        forall |k:int| 0 <= k < i ==> b[k] == 1,
        b[(i as int)] == 1,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> b[k] == 1,
{
    assert forall |k:int| 0 <= k < i + 1 implies b[k] == 1 by {
        if 0 <= k < i {
            assert(b[k] == 1);
        } else {
            assert(k == i) by {
                assert(k < i + 1);
                assert(!(k < i));
                assert(k >= i);
            }
            assert(b[k] == b[(i as int)]);
            assert(b[(i as int)] == 1);
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    sum.set(0, 0);

    let mut i: usize = 0;
    while (i < (N as usize))
        invariant
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
    {
        a.set(i, 1);

        assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == 1) by {
            lemma_extend_prefix_set_to_one_a(a, i);
        };

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        invariant
            i <= (N as usize),
            sum.len() == 1,
            a.len() == N,
            sum[0] == i,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
    {
        let temp = sum[0] + a[i];
        sum.set(0, temp);

        assert(sum[0] == i + 1);

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        invariant
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 1,
    {
        b.set(i, 1);

        assert(forall |k:int| 0 <= k < i + 1 ==> b[k] == 1) by {
            lemma_extend_prefix_set_to_one_b(b, i);
        };

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        invariant
            i <= (N as usize),
            sum.len() == 1,
            b.len() == N,
            sum[0] == N + i,
            forall |k:int| 0 <= k < N ==> b[k] == 1,
            N < 1000,
    {
        let temp = sum[0] + b[i];
        sum.set(0, temp);

        assert(sum[0] == N + (i + 1));

        i = i + 1;
    }

    assert(sum[0] <= 2 * N);
}
}