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

// Complete the lemma function below
proof fn lemma_forall_extend_by_last_set_to_2(a_old: Seq<i32>, i_old: int, idx_set: int)
   

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
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof;

		let ghost old_view = a@;
		// Fill in a block of assertions here to complete the proof

		a.set(i, 2);

		let ghost new_view = a@;
		// Fill in a block of assertions here to complete the proof;

		let ghost i_old: int = (i as int);
		i = i + 1;

		assert(forall |k:int| 0<= k < i ==> a[k] == 2) by {
            assert((i as int) == i_old + 1);
            assert(new_view == old_view.update(i_old, 2));

            assert(0 <= i_old);
            assert(i_old < old_view.len());

            lemma_forall_extend_by_last_set_to_2(old_view, i_old, i_old);

            assert(forall|k:int| 0 <= k < (i as int) ==> new_view[k] == 2) by {
                let k: int;
                if 0 <= k < (i as int) {
                    assert((i as int) == i_old + 1);
                    assert(k < i_old + 1);
                    assert(old_view.update(i_old, 2)[k] == 2) by {
                        assert(0 <= k < i_old + 1);
                        assert(forall|t:int| 0 <= t < i_old + 1 ==> old_view.update(i_old, 2)[t] == 2);
                    }
                    assert(new_view == old_view.update(i_old, 2));
                    assert(new_view[k] == old_view.update(i_old, 2)[k]);
                    assert(new_view[k] == 2);
                }
            };

            assert(forall|k:int| 0 <= k < i ==> a[k] == 2) by {
                let k: int;
                if 0 <= k < i {
                    assert(new_view[k] == 2);
                    assert(a@[k] == 2);
                }
            }
		}
	}

	// Fill in a block of assertions here to complete the proof

	i = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		// Fill in a block of assertions here to complete the proof

		if (a[i] == 2) {
            // Fill in a block of assertions here to complete the proof

			let sum_before_set = sum[0];
			let temp = sum[0] + a[i];

			// Fill in a block of assertions here to complete the proof;

			let ghost sum_view_before = sum@;
			// Fill in a block of assertions here to complete the proof;

			sum.set(0, temp);

			let ghost sum_view_after = sum@;
			assert(sum_view_after == sum_view_before.update(0, temp));
			assert(sum_view_after[0] == temp);

			assert(sum[0] == temp);

			assert(sum[0] == 2 * i + 2) by {
				assert(sum_before_set == 2 * i);
				assert(a[(i as int)] == 2);
				assert(temp == sum_before_set + a[(i as int)]);
				assert(sum[0] == temp);
			}

			assert((sum[0] as int) == 2 * (i as int) + 2) by {
				assert(sum[0] == 2 * i + 2);
			}

            assert((sum[0] as int) == 2 * ((i as int) + 1)) by {
                assert((sum[0] as int) == 2 * (i as int) + 2);
            };
		} else {
			// Fill in a block of assertions here to complete the proof
			let temp = sum[0] * a[i];
			sum.set(0, temp);
		}

		let iprev_usize = i;
		i = i + 1;

		// Fill in a block of assertions here to complete the proof
	}

	assert(i == N as usize);
	assert(sum[0] == 2 * (N as usize)) by {
		assert(sum[0] == 2 * i);
	}
	assert(sum[0] == 2 * N);
}
}