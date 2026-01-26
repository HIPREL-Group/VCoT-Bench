use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_update_forall_extend_i32(s: Seq<i32>, i: int, v: i32, p: spec_fn(int) -> bool)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_last_i32(v: &Vec<i32>, i: usize, val: i32)
   

proof fn lemma_forall_shrink_from_i_i32(v: &Vec<i32>, i: usize, n: i32)
    requires
        i < (n as usize),
        forall|j: int| i <= j < n ==> v[j] == 1,
    ensures
        forall|j: int| i + 1 <= j < n ==> v[j] == 1,
{
    assert forall|j: int| i + 1 <= j < n implies v[j] == 1 by {
        if i + 1 <= j < n {
            assert(v[j] == 1);
        }
    };
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 6 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < (N as usize))
		// Fill in loop invariants here
	{
		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof

		if (a[i] == 1) {
			let temp = a[i];
			a.set(i, temp + 5);
		} else {
			let temp = a[i];
			a.set(i, temp - 1);
		}

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof;

		let temp = sum[0] + a[i];

		sum.set(0, temp);

		assert(sum[0] == 6 * (i + 1)) by {
			assert(sum[0] == (6 * i) + 6) by {
				assert(sum[0] == 6 * i + 6);
			};
			assert(6 * (i + 1) == (6 * i) + 6);
		};

		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof;
}
}