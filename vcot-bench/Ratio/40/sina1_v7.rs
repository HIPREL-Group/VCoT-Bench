use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_vec_len_eq_one_view_index0<T>(v: &Vec<T>)
   

// Complete the lemma function below
proof fn lemma_usize_lt_from_i32_lt(i: usize, n: i32)
   

proof fn lemma_i32_ge0_from_usize_le_cast(i: usize, n: i32)
    requires
        n > 0,
        i <= (n as usize),
    ensures
        0 <= (i as int),
        0 <= (n as int),
{
    assert(0 <= (i as int));
    assert(0 <= (n as int)) by {
        assert(n > 0);
    }
}

// Complete the lemma function below
proof fn lemma_vec_set_updates_only_index<T>(v: &Vec<T>, i: usize, val: T)
   

// Complete the lemma function below
proof fn lemma_i_lt_len_implies_index_int_lt_len<T>(v: &Vec<T>, i: usize)
   

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < (N as usize))
		// Fill in loop invariants here
		decreases
			(N as int) - (i as int),
	{
		proof {
			lemma_vec_len_eq_one_view_index0(sum);
		}

		let temp = sum[0];

		// Fill in a block of assertions here to complete the proof

		sum.set(0, temp + 1);

		proof {
            assert((sum[0] as int) == (i as int) + 1);
		}

		i = i + 1;

		proof {
            lemma_i32_ge0_from_usize_le_cast(i, N);
		}
	}

	proof {
		lemma_vec_len_eq_one_view_index0(sum);
	}

	i = 0;
	while (i < (N as usize))
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == sum[0],
			sum.len() == 1,
			a.len() == N,
			i <= N,
		decreases
			(N as int) - (i as int),
	{
		// Fill in a block of assertions here to complete the proof

		let temp = sum[0];

		proof {
			assert(temp == sum[0]);
		}

        let ghost a_pre = a@;

		a.set(i, temp);

		proof {
			assert(a[(i as int)] == sum[0]);
			assert(forall |k:int| 0 <= k < i ==> a[k] == sum[0]) by {
                assert(forall |k:int| 0 <= k < i ==> a_pre[k] == sum[0]);
                assert(forall |k:int| 0 <= k < i ==> a[k] == a_pre[k]);
            }

            lemma_i_lt_len_implies_index_int_lt_len(a, i);

			assert(forall |k:int| 0 <= k < i + 1 ==> a[k] == sum[0]);
		}

		i = i + 1;
	}

	proof {
		assert(i == (N as usize));
		assert(sum.len() == 1);
		assert(sum[0] == N);
		assert(forall |k:int| 0 <= k < N ==> a[k] == sum[0]);
		assert(forall |k:int| 0 <= k < N ==> a[k] == N);
	}
}
}