use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_i32_add_overflow_free_for_sum_progress(i: int, n: int)
    requires
        0 <= i,
        i < n,
        n < 1000,
    ensures
        -2147483648 <= 2 * i,
        2 * i <= 2147483647 - 2,
{
    assert(2 * i <= 2 * 999) by {
        assert(i <= 999);
    }
    assert(2 * 999 == 1998);
    assert(1998 <= 2147483645);
    assert(-2147483648 <= 2 * i) by {
        assert(0 <= 2 * i);
    }
}

proof fn lemma_forall_extend_by_last_set_to_2(a_old: Seq<i32>, i_old: int, idx_set: int)
    requires
        0 <= i_old,
        idx_set == i_old,
        0 <= idx_set < a_old.len(),
        forall|k:int| 0 <= k < i_old ==> a_old[k] == 2,
    ensures
        forall|k:int| 0 <= k < i_old + 1 ==> a_old.update(idx_set, 2)[k] == 2,
{
    assert(forall|k:int| 0 <= k < i_old + 1 ==> a_old.update(idx_set, 2)[k] == 2) by {
        let k: int;
        if 0 <= k < i_old + 1 {
            if k == idx_set {
                assert(a_old.update(idx_set, 2)[k] == 2);
            } else {
                assert(k < i_old) by {
                    assert(k <= i_old);
                    assert(k != i_old);
                    assert(idx_set == i_old);
                }
                assert(0 <= k < i_old);
                assert(a_old.update(idx_set, 2)[k] == a_old[k]);
                assert(a_old[k] == 2);
                assert(a_old.update(idx_set, 2)[k] == 2);
            }
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
		sum[0] == 2 * N,
{
	sum.set(0, 0);

	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 2,
			a.len() == N,
			0 <= i <= N,
	{
		// Fill in a block of assertions here to complete the proof;

		let ghost old_view = a@;
		assert(0 <= (i as int));
		assert((i as int) < old_view.len()) by {
			assert(old_view.len() == a.len());
			// Fill in a block of assertions here to complete the proof;
		}

		a.set(i, 2);

		let ghost new_view = a@;
		// Fill in a block of assertions here to complete the proof;

		let ghost i_old: int = (i as int);
		i = i + 1;

		// Fill in a block of assertions here to complete the proof
	}

	// Fill in a block of assertions here to complete the proof

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 2,
			a.len() == N,
			sum[0] == 2 * i,
			sum.len() == 1,
			N < 1000,
	{
		// Fill in a block of assertions here to complete the proof;

		assert(a[(i as int)] == 2) by {
			assert(0 <= (i as int));
			assert((i as int) < (N as int)) by {
				assert(i < N as usize);
			}
			assert(a[i as int] == 2);
		}

		if (a[i] == 2) {
            // Fill in a block of assertions here to complete the proof

			let sum_before_set = sum[0];
			let temp = sum[0] + a[i];

			// Fill in a block of assertions here to complete the proof;

			let ghost sum_view_before = sum@;
			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			let ghost sum_view_after = sum@;
			// Fill in a block of assertions here to complete the proof;
		} else {
			// Fill in a block of assertions here to complete the proof
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		let iprev_usize = i;
		i = i + 1;

		// Fill in a block of assertions here to complete the proof
	}

	// Fill in a block of assertions here to complete the proof;
}
}