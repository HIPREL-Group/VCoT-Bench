use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_forall_extend_prefix_update_to_one(a_old: Seq<i32>, i: usize)
    requires
        (i as int) < a_old.len(),
        forall |j: int| 0 <= j < (i as int) ==> a_old[j] == 1,
    ensures
        forall |j: int| 0 <= j < ((i + 1) as int) ==> a_old.update((i as int), 1)[j] == 1,
{
    assert forall |j: int| 0 <= j < ((i + 1) as int) implies a_old.update((i as int), 1)[j] == 1 by {
        if j < (i as int) {
            assert(0 <= j < (i as int));
            assert(a_old[j] == 1);
            assert(a_old.update((i as int), 1)[j] == a_old[j]) by {
                assert(j != (i as int));
            }
            assert(a_old.update((i as int), 1)[j] == 1);
        } else {
            assert(j == (i as int)) by {
                assert(j <= (i as int)) by {
                    assert(j < (i as int) + 1);
                };
            };
            assert(a_old.update((i as int), 1)[j] == 1);
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
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
    while (i < (N as usize))
        invariant
            forall |j: int| 0 <= j < i ==> a[j] == 1,
            a.len() == N,
    {
        // Fill in a block of assertions here to complete the proof;

        let ghost prev_a_view = a@;

        a.set(i, 1);

        assert(a@ == prev_a_view.update((i as int), 1));

        proof {
            assert(forall |j: int| 0 <= j < ((i + 1) as int) ==> a@[j] == 1) by {
                lemma_forall_extend_prefix_update_to_one(prev_a_view, i);
                assert(a@ == prev_a_view.update((i as int), 1));
            };
        }

        i = i + 1;

        assert(forall |j: int| 0 <= j < i ==> a[j] == 1);
        assert(a.len() == N);
    }

    i = 0;
    while (i < (N as usize))
        invariant
            forall |j: int| 0 <= j < i ==> a[j] == 3,
            forall |j: int| i <= j < N ==> a[j] == 1,
            a.len() == N,
    {
        // Fill in a block of assertions here to complete the proof;

        assert(a@[(i as int)] == 1);

        if (a[i] == 1) {
            let temp = a[i];
            a.set(i, temp + 2);
            assert(a@[(i as int)] == 3) by {
                assert(temp == 1);
            };
        } else {
            let temp = a[i];
            a.set(i, temp - 1);
        }

        proof {
            assert(a@[(i as int)] == 3);

            assert forall |j: int| 0 <= j < ((i + 1) as int) implies a@[j] == 3 by {
                if j < (i as int) {
                    assert(0 <= j < (i as int));
                    assert(a@[j] == 3);
                } else {
                    assert(j == (i as int)) by {
                        assert(j <= (i as int)) by {
                            assert(j < (i as int) + 1);
                        };
                    };
                    assert(a@[j] == 3);
                }
            }

            assert forall |j: int| ((i + 1) as int) <= j < N implies a@[j] == 1 by {
                assert(a@[j] == 1);
            }
        }

        i = i + 1;
    }

    i = 0;
    while (i < (N as usize))
        invariant
            i <= N,
            forall |j: int| 0 <= j < N ==> a[j] == 3,
            sum.len() == 1,
            sum[0] == 3 * i,
            N <= 1000,
            a.len() == N,
    {
        // Fill in a block of assertions here to complete the proof;

        let temp = sum[0] + a[i];
        // Fill in a block of assertions here to complete the proof;
        sum.set(0, temp);
        assert(sum[0] == 3 * ((i + 1) as int)) by {
            assert(temp == 3 * (i as int) + 3);
            assert(3 * ((i + 1) as int) == 3 * (i as int) + 3);
        };

        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof;
}

}