use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_vec_len_eq_one_view_index0<T>(v: &Vec<T>)
    requires
        v.len() == 1,
    ensures
        v@.len() == 1,
{
    assert(v@.len() == v.len());
    assert(v@.len() == 1);
}

proof fn lemma_usize_lt_from_i32_lt(i: usize, n: i32)
    requires
        i < (n as usize),
        n > 0,
    ensures
        (i as int) < (n as int),
        0 <= (i as int),
{
    assert(0 <= (i as int));
    assert((i as int) < (n as int)) by {
        assert((i as int) < ((n as usize) as int));
        assert(((n as usize) as int) == (n as int)) by {
            assert((n as int) >= 0);
        }
    }
}

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

proof fn lemma_vec_set_updates_only_index<T>(v: &Vec<T>, i: usize, val: T)
    requires
        i < v.len(),
    ensures
        (v@.update((i as int), val)).len() == v@.len(),
        forall|k:int| 0 <= k < v@.len() && k != (i as int) ==> v@.update((i as int), val)[k] == v@[k],
        v@.update((i as int), val)[(i as int)] == val,
{
    assert((v@.update((i as int), val)).len() == v@.len());
    assert(v@.update((i as int), val)[(i as int)] == val);
    assert(forall|k:int| 0 <= k < v@.len() && k != (i as int) ==> v@.update((i as int), val)[k] == v@[k]) by {
        assert(forall|k:int| 0 <= k < v@.len() && k != (i as int) ==> v@.update((i as int), val)[k] == v@[k]) by {
        }
    }
}

proof fn lemma_i_lt_len_implies_index_int_lt_len<T>(v: &Vec<T>, i: usize)
    requires
        i < v.len(),
    ensures
        (i as int) < v@.len(),
{
    assert(v@.len() == v.len());
    assert((i as int) < (v.len() as int)) by {
        assert(i < v.len());
    }
    assert((i as int) < v@.len());
}

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
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i,
		decreases
			(N as int) - (i as int),
	{
		proof {
			lemma_vec_len_eq_one_view_index0(sum);
		}

		let temp = sum[0];

		proof {
            assert(i < (N as usize) ==> (i as int) < (N as int)) by {
                if i < (N as usize) {
                    lemma_usize_lt_from_i32_lt(i, N);
                }
            }
		}

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
		proof {
			lemma_vec_len_eq_one_view_index0(sum);
            assert(i < (N as usize) ==> (i as int) < (N as int)) by {
                if i < (N as usize) {
                    lemma_usize_lt_from_i32_lt(i, N);
                }
            }
		}

		let temp = sum[0];

		// Fill in a block of assertions here to complete the proof

        let ghost a_pre = a@;

		a.set(i, temp);

		// Fill in a block of assertions here to complete the proof

		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof
}
}