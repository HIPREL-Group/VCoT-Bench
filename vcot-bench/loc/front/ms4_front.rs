use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_step_sum_bound(prev_sum: int, a_i: int, i: int)
    requires
        i > 0,
        prev_sum <= 3 * i,
        0 <= a_i,
        a_i <= 3,
    ensures
        prev_sum + a_i <= 3 * (i + 1)
{
    assert(prev_sum + a_i <= 3 * i + 3);
    assert(3 * i + 3 == 3 * (i + 1)) by (nonlinear_arith);
}

proof fn lemma_forall_extend_by_new_index_i32(a: &Vec<i32>, i: usize)
    requires
        i < a.len(),
        forall |k:int| 0 <= k < i ==> a[k] == k % 4,
        a[i as int] == (i as int) % 4,
    ensures
        forall |k:int| 0 <= k < i + 1 ==> a[k] == k % 4
{
    assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == k % 4) by {
        assert_forall_by(|k:int| {
            requires(0 <= k < i + 1);
            ensures(a[k] == k % 4);
            if k < i {
                assert(a[k] == k % 4);
            } else {
                assert(k == i as int);
                assert(a[k] == a[i as int]);
                assert(a[i as int] == (i as int) % 4);
                assert(k % 4 == (i as int) % 4);
            }
        });
    };
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		// Fill in loop invariants here
	{
		a.set(i, (i % 4) as i32);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		// Fill in loop invariants here
	{
		if (i == 0) {
			sum.set(0, 0);
			// Fill in a block of assertions here to complete the proof;
		} else {
			assert(0 <= a[(i as int)]) by {
				assert(0 <= (i as int) % 4) by (nonlinear_arith);
				assert(a[i as int] == (i as int) % 4);
				assert(0 <= a[(i as int)] as int);
			}
			assert(a[(i as int)] <= 3) by {
				assert((i as int) % 4 <= 3) by (nonlinear_arith);
				assert(a[i as int] == (i as int) % 4);
				assert(a[(i as int)] as int <= 3);
			}

			let temp = sum[0] + a[i];

			assert(sum[0] + a[(i as int)] <= 3 * (i as int + 1)) by {
				let prev_sum: int = sum[0] as int;
				let ai: int = a[(i as int)] as int;

				assert(prev_sum <= 3 * (i as int)) by {
					assert(sum[0] <= 3 * i);
				}
				assert(0 <= ai) by { assert(0 <= a[(i as int)]); }
				assert(ai <= 3) by { assert(a[(i as int)] <= 3); }
				lemma_step_sum_bound(prev_sum, ai, i as int);
			};

			sum.set(0, temp);

			assert(sum[0] as int <= 3 * ((i as int) + 1));
		}

		assert(i + 1 <= N);

		i = i + 1;

		assert(i <= N);
	}

	assert(i == N as usize);

	if i > 0 {
		assert(sum[0] <= 3 * (i as i32));
	}
	assert(sum[0] <= 3 * N);
}
}