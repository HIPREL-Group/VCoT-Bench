use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_seq_update_preserves_prefix_when_value_known(
    s0: Seq<i32>,
    i: usize,
    v: i32,
)
    requires
        i < s0.len(),
        forall|j: int| 0 <= j < (i as int) ==> s0.index(j) == v,
    ensures
        forall|j: int| 0 <= j < (i as int) ==> s0.update(i as int, v).index(j) == v,
{
    assert forall|j: int| 0 <= j < (i as int) implies s0.update(i as int, v).index(j) == v by {
        assert(0 <= j < s0.len());
        assert(j != (i as int));
    }
}

proof fn lemma_seq_update_preserves_prefix_4(
    s0: Seq<i32>,
    i: usize,
    new_val: i32,
)
    requires
        i < s0.len(),
        forall|j: int| 0 <= j < (i as int) ==> s0.index(j) == 4,
    ensures
        forall|j: int| 0 <= j < (i as int) ==> s0.update(i as int, new_val).index(j) == 4,
{
    assert forall|j: int| 0 <= j < (i as int) implies s0.update(i as int, new_val).index(j) == 4 by {
        assert(0 <= j < s0.len());
        assert(j != (i as int));
        assert(s0.update(i as int, new_val).index(j) == s0.index(j));
        assert(s0.index(j) == 4);
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
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N as usize)
		invariant
			forall |j: int| 0<= j < i ==> a[j] == 1,
			a.len() == N,
	{
		a.set(i, 1);

		i = i + 1;

		proof {
			let s1 = a@;
			let ii_prev: int = (i as int) - 1;
			assert(s1.index(ii_prev) == 1);
		}
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |j: int| 0<= j < i ==> a[j] == 4,
			forall |j: int| i <= j < N ==> a[j] == 1,
			a.len() == N,
	{
		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 3);
			// Fill in a block of assertions here to complete the proof;
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
			// Fill in a block of assertions here to complete the proof;
		}

		proof {
			let s1 = a@;
			let ii: int = (i as int);
			assert(s1.index(ii) == 4);

			assert(forall |j: int| 0 <= j < i ==> s1.index(j) == 4);
		}

		i = i + 1;

		// Fill in a block of assertions here to complete the proof
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let temp = sum[0] + a[i];
		sum.set(0, temp);

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof;
}
}