use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_mod2_add_1(x: int)
    ensures
        ((x + 1) % 2) == ((x % 2) + 1) % 2,
{
    vstd::arithmetic::div_mod::lemma_mod_adds(x, 1, 2);
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, N: u32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
	let mut i: usize = 0;

	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, 0);

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (N % 2 == 0) {
            let temp = a[i];
            assert((temp as int) == 0) by {
                assert((i as int) < (N as int)) by {
                    assert(i < N as usize);
                }
                assert(a[(i as int)] == 0);
            }

			a.set(i, temp + 2);

            assert(a[(i as int)] % 2 == (N as int) % 2) by {
                assert(N % 2 == 0);
                assert(a[(i as int)] == (temp + 2)) by { }
                vstd::arithmetic::div_mod::lemma_mod_adds((temp as int), 2, 2);
                assert((temp as int) % 2 == 0) by { }
            }
		} else {
            let temp = a[i];
            assert((temp as int) == 0) by {
                assert((i as int) < (N as int)) by {
                    assert(i < N as usize);
                }
                assert(a[(i as int)] == 0);
            }

			a.set(i, temp + 1);

            // Fill in a block of assertions here to complete the proof
		}

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}
}
}