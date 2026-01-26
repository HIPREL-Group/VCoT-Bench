use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_forall_prefix_update_to_1(old_a: Seq<i32>, new_a: Seq<i32>, idx: int, old_i: int)
   

// Complete the lemma function below
proof fn lemma_forall_prefix_update_to_5(old_a: Seq<i32>, new_a: Seq<i32>, idx: int, old_i: int)
   

// Complete the lemma function below
proof fn lemma_forall_suffix_shrink(old_a: Seq<i32>, i0: int, n: int)
   

// Complete the lemma function below
proof fn lemma_update_preserves_suffix_except_at_idx(old_a: Seq<i32>, idx: int, n: int)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 5 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, 1);

		let ghost old_i: int = i as int;
		let ghost old_view = a@;

		i = i + 1;

		assert(forall |j: int| 0 <= j < i ==> a[j] == 1) by {
			let prev_i: int = (i as int) - 1;
			assert(prev_i == old_i);

			assert(a[prev_i] == 1) by {
				assert(a@ == old_view.update(old_i, 1));
			};

			lemma_forall_prefix_update_to_1(old_view, a@, old_i, old_i);
		};
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let ghost old_i: int = i as int;
		let ghost old_view = a@;

		if (a[i] == 1) {
			let temp = a[i];

			a.set(i, temp + 4);

			// Fill in a block of assertions here to complete the proof;
		} else {
			let temp = a[i];
			// Fill in a block of assertions here to complete the proof;
			a.set(i, temp - 1);
		}

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let ghost old_i: int = i as int;

		let temp = sum[0] + a[i];

		// Fill in a block of assertions here to complete the proof;

		sum.set(0, temp);

		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof;
}
}