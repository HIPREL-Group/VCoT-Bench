use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_extend_by_one(a: &Vec<u32>, i: usize)
    requires
        forall|j:int| 0 <= j < i ==> a[j] <= 2,
        i < a.len(),
        a[(i as int)] <= 2,
    ensures
        forall|j:int| 0 <= j < i + 1 ==> a[j] <= 2,
{
    assert(forall|j:int| 0 <= j < i + 1 ==> a[j] <= 2) by {
        assert forall|j:int| 0 <= j < i + 1 implies a[j] <= 2 by {
            if j < i as int {
                assert(a[j] <= 2);
            } else {
                assert(j == i as int);
                assert(a[j] == a[(i as int)]) by { }
                assert(a[j] <= 2);
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    ensures
        sum <= 2*N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len()==N,
            forall|j:int| 0<=j<i ==> a[j]<=2,
    {
        assert(i < a.len());
        assert(i < N as usize);

        if (a[i] > 2) {
            a.set(i, 2);
            assert(a[(i as int)] == 2);
            assert(a[(i as int)] <= 2);
        } else {
            assert(a[(i as int)] <= 2);
        }

        assert(forall|j:int|
            0 <= j < i + 1 ==> a[j] <= 2
        ) by {
            lemma_forall_extend_by_one(a, i);
        };

        i = i + 1;
    }

    i = 0;
    let mut sum: u32 = 0;

    while (i < N as usize)
        invariant
            i<=N,
            N <= 0x7FFF_FFFF,
            a.len()==N,
            forall|j:int| 0<=j<N ==> a[j]<=2,
            sum<=2 * i,
    {
        assert(i < a.len());
        assert(i < N as usize);

        assert(a[(i as int)] <= 2);

        assert(sum + a[(i as int)] <= 2 * (i as u32 + 1));

        sum = sum + a[i];
        i = i + 1;

        assert(sum <= 2 * (i as u32));
        assert(i <= N);

        assert(sum <= 2 * i) by { }
    }

    assert(i == N as usize) by {
        assert(i <= N as usize);
        assert(!(i < N as usize));
    }
    assert(sum <= 2 * N) by {
        assert(sum <= 2 * (i as u32));
        assert(i as u32 == N);
        assert(2 * (i as u32) == 2 * N);
    }

    sum
}

}