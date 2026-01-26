use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_push_forall_prefix_after_set(v: &Vec<i32>, i: usize)
    requires
        i < v.len(),
        forall |k:int| 0 <= k < i as int ==> v[k] == 1,
        v[i as int] == 1,
    ensures
        forall |k:int| 0 <= k < (i as int) + 1 ==> v[k] == 1,
{
    assert(v[i as int] == 1);
    assert(forall |k:int| 0 <= k < i as int ==> v[k] == 1);

    assert(forall |k:int| 0 <= k < (i as int) + 1 ==> v[k] == 1) by {
        assert(forall |k:int| 0 <= k < (i as int) + 1 ==> v[k] == 1) by {
            assert(forall |k:int| 0 <= k < (i as int) + 1 ==> v[k] == 1) by {
                assert forall |k:int| 0 <= k < (i as int) + 1 implies v[k] == 1 by {
                    if k < i as int {
                        assert(v[k] == 1) by {
                            assert(0 <= k < i as int ==> v[k] == 1);
                        }
                    } else {
                        assert(k == i as int) by {
                            assert(k <= i as int) by {
                                assert(k < i as int + 1);
                            }
                        }
                        assert(v[k] == 1) by {
                            assert(k == i as int);
                            assert(v[i as int] == 1);
                        }
                    }
                }
            };
        };
    };
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
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			a.len() == N,
			forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		b.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i,
            a.len() == N,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
	{
        let temp = sum[0] + a[i];
		sum.set(0, temp);

        i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
            b.len() == N,
			sum[0] == N + i,
            N < 1000,
			forall |k:int| 0 <= k < N ==> b[k] == 1,
	{
		let temp = sum[0] + b[i];
		sum.set(0, temp);

		i = i + 1;
	}

    // Fill in a block of assertions here to complete the proof
}
}