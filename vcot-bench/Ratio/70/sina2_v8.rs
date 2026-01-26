use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_vec_set_updates_view_at_i32(v: Seq<i32>, i: int, val: i32)
   

// Complete the lemma function below
proof fn lemma_vec_set_gives_value_i32(v: Seq<i32>, i: int, val: i32)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			sum[0] == i,
			a.len() == N,
			sum.len() == 1,
	{
		let temp = sum[0] + a[i];

		// Fill in a block of assertions here to complete the proof;

		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		let temp = a[i] + sum[0];

		// Fill in a block of assertions here to complete the proof;

		a.set(i, temp);

        proof { lemma_vec_set_gives_value_i32(a@, (i as int), temp); }
		assert(a[i as int] == N + 1) by {
			assert(temp == N + 1);
		};

		assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == N + 1) by {
			assert forall |k:int| 0 <= k < i + 1 implies a[k] == N + 1 by {
				if k < i as int {
					assert(a[k] == N + 1);
				} else {
					assert(k == i as int);
					assert(a[k] == a[i as int]);
					assert(a[i as int] == N + 1);
				}
			}
		};

		assert(forall |k:int| i + 1 <= k < N ==> a[k] == 1) by {
			assert forall |k:int| i + 1 <= k < N implies a[k] == 1 by {
				assert(a[k] == 1);
			}
		};

		i = i + 1;
	}

	assert(forall |k:int| 0 <= k < N ==> a[k] == N + 1) by {
		assert forall |k:int| 0 <= k < N implies a[k] == N + 1 by {
			assert(a[k] == N + 1);
		}
	};
}
}