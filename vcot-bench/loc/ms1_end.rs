use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_forall_extend_one(a: &Vec<usize>, i: usize, v: usize)
    requires
        a.len() > 0,
        i < a.len(),
        forall |k: int| 0 <= k < i ==> a[k] == v,
        a[i as int] == v,
    ensures
        forall |k: int| 0 <= k < i + 1 ==> a[k] == v,
{
    assert(forall |k: int| 0 <= k < i + 1 ==> a[k] == v) by {
        assert forall |k: int| 0 <= k < i + 1 implies a[k] == v by {
            if k < i {
                assert(a[k] == v);
            } else {
                assert(k == i);
                assert(a[k] == v);
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] == 0,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k: int| 0<= k < i ==> a[k] == 0,
			a.len() == N,
	{
        let tmp: usize = i % 1;
        assert(tmp == 0);

		a.set(i, tmp);

        proof {
            lemma_forall_extend_one(a, i, 0);
        }

		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
		invariant
			forall |k: int| 0<= k < N ==> a[k] == 0,
			a.len() == N,
			i > 0 ==> sum[0] == 0,
			sum.len() == 1,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
            let temp = sum[0] + a[i];
            // Fill in a block of assertions here to complete the proof;
			sum.set(0, temp);
		}
		i = i + 1;
	}
}
}