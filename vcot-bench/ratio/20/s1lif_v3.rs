use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall |j: int| 0<= j < i ==> a[j] == 1,
    {
        a.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall |j: int| 0<= j < i ==> a[j] == 2,
            forall |j: int| i<= j < N ==> a[j] == 1,
    {
        assert(a[i as int] == 1) by {
            assert(forall |j: int| i <= j < N ==> a[j] == 1);
        };

        if (a[i] == 1) {
            let temp = a[i] + 1;
            a.set(i, temp);
            assert(a[i as int] == 2);
        } else {
            assert(false) by {
                assert(a[i as int] == 1);
            };
            let temp = a[i] - 1;
            a.set(i, temp);
        }

        assert(forall |j: int| 0 <= j < i + 1 ==> a[j] == 2) by {
            assert(a[i as int] == 2);

            assert forall |j: int| 0 <= j < i + 1 implies a[j] == 2 by {
                if j < i {
                    assert(a[j] == 2);
                } else {
                    assert(j == i as int);
                    assert(a[i as int] == 2);
                }
            }
        };
        assert(forall |j: int| (i + 1) <= j < N ==> a[j] == 1) by {
            assert forall |j: int| (i + 1) <= j < N implies a[j] == 1 by {
                assert(a[j] == 1);
            }
        };

        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        // Fill in loop invariants here
    {
        assert(a[i as int] == 2) by {
            assert(forall |j: int| 0 <= j < N ==> a[j] == 2);
        };

        let temp = sum[0] + a[i];
        assert(temp == 2 * (i + 1)) by {
            assert(sum[0] == 2 * i);
            assert(a[i as int] == 2);
        };
        sum.set(0, temp);

        assert(sum[0] == 2 * (i + 1)) by {
            assert(sum[0] == temp);
            assert(temp == 2 * (i + 1));
        };

        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof;
}
}