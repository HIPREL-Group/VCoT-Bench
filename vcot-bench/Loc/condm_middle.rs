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
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 0,
			a.len() == N,
	{
		a.set(i, 0);

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] % 2 == N % 2,
			forall |k:int| i <= k < N ==> a[k] == 0,
			a.len() == N,
	{
		if (N % 2 == 0) {
            let temp = a[i];
            // Fill in a block of assertions here to complete the proof

			a.set(i, temp + 2);

            // Fill in a block of assertions here to complete the proof
		} else {
            let temp = a[i];
            // Fill in a block of assertions here to complete the proof

			a.set(i, temp + 1);

            assert(a[(i as int)] % 2 == (N as int) % 2) by {
                assert(N % 2 != 0);
                assert(a[(i as int)] == (temp + 1)) by { }
                lemma_mod2_add_1((temp as int));
                assert((temp as int) % 2 == 0) by { }
                vstd::arithmetic::div_mod::lemma_mod_bound((N as int), 2);
            }
		}

        assert(forall |k:int| 0 <= k < i + 1 ==> a[k] % 2 == N % 2) by {
            assert(forall |k:int| 0 <= k < i ==> a[k] % 2 == N % 2);
            assert(a[(i as int)] % 2 == (N as int) % 2);
        }
        
        assert(forall |k:int| (i + 1) <= k < N ==> a[k] == 0);

		i = i + 1;
	}
}
}