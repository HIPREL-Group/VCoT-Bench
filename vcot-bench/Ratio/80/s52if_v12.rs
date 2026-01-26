use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_seq_update_extends_forall_prefix_1(old_s: Seq<i32>, new_s: Seq<i32>, i0: int)
    requires
        0 <= i0,
        new_s == old_s.update(i0, 1),
        forall |k:int| 0 <= k < i0 ==> old_s[k] == 1,
        i0 < old_s.len(),
    ensures
        forall |k:int| 0 <= k < i0 + 1 ==> new_s[k] == 1,
{
    assert forall |k:int| 0 <= k < i0 + 1 implies new_s[k] == 1 by {
        if k < i0 {
            assert(old_s[k] == 1);

            assert(k != i0);
            assert(new_s[k] == old_s[k]);
        } else {
            assert(k == i0);
            assert(new_s[i0] == 1);
        }
    }
}

// Complete the lemma function below
proof fn lemma_vec_set_view_update_i32(v: &Vec<i32>, i: usize, val: i32)
   

// Complete the lemma function below
proof fn lemma_second_loop_if_branch_sets_i_to_6(a: &Vec<i32>, i: usize)
   

proof fn lemma_second_loop_else_branch_sets_i_to_5(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        a[(i as int)] == 6,
    ensures
        a@.update((i as int), (a[(i as int)] - 1) as i32)[(i as int)] == 5,
{
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
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

	while (i < N)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
	{
		let old_view = Ghost(a@);
		a.set(i, 1);

        // Fill in a block of assertions here to complete the proof;

		i = i + 1;

        // Fill in a block of assertions here to complete the proof
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		if (a[i] == 1) {
			let temp = a[i];
            // Fill in a block of assertions here to complete the proof
			a.set(i, temp + 5);
		} else {
			let temp = a[i];
            // Fill in a block of assertions here to complete the proof
			a.set(i, temp - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof;

		if (a[i] == 6)
		{
			let temp = sum[0] + a[i];
			sum.set(0, temp);
			// Fill in a block of assertions here to complete the proof
		} else {
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}
		i = i + 1;

		// Fill in a block of assertions here to complete the proof;
	}

	// Fill in a block of assertions here to complete the proof;
}
}