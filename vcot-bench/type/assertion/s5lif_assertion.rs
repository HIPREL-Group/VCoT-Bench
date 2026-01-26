use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_update_forall_extend_i32(s: Seq<i32>, i: int, v: i32, p: spec_fn(int) -> bool)
    requires
        0 <= i < s.len(),
        p(i),
        forall|j: int| 0 <= j < s.len() && j != i ==> #[trigger] p(j),
    ensures
        forall|j: int| 0 <= j < s.len() ==> s.update(i, v).index(j) == if j == i { v } else { s.index(j) },
        p(i),
{
    assert forall|j: int| 0 <= j < s.len() implies s.update(i, v).index(j) == if j == i { v } else { s.index(j) } by {
        if 0 <= j < s.len() {
            if j == i {
                assert(s.update(i, v).index(j) == v);
            } else {
                assert(s.update(i, v).index(j) == s.index(j));
            }
        }
    };
}

proof fn lemma_forall_extend_by_last_i32(v: &Vec<i32>, i: usize, val: i32)
    requires
        i < v.len(),
        forall|j: int| 0 <= j < i ==> v[j] == val,
        v[(i as int)] == val,
    ensures
        forall|j: int| 0 <= j < i + 1 ==> v[j] == val,
{
    assert forall|j: int| 0 <= j < i + 1 implies v[j] == val by {
        if 0 <= j < i + 1 {
            if j < i {
                assert(v[j] == val);
            } else {
                assert(v[j] == val);
            }
        }
    };
}

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
		invariant
			forall |j: int| 0<= j < i ==> a[j] == 1,
			a.len() == N,
	{
		a.set(i, 1);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	i = 0;
	while (i < (N as usize))
		invariant
			forall |j: int| 0<= j < i ==> a[j] == 6,
			forall |j: int| i <= j < N ==> a[j] == 1,
			a.len() == N,
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
		invariant
			i <= N,
			forall |j: int| 0<= j < N ==> a[j] == 6,
			sum[0] == 6 * i,
			sum.len() == 1,
			a.len() == N,
			N < 1000,
	{
		// Fill in a block of assertions here to complete the proof;

		let temp = sum[0] + a[i];

		sum.set(0, temp);

		// Fill in a block of assertions here to complete the proof;

		i = i + 1;
	}

	// Fill in a block of assertions here to complete the proof;
}
}