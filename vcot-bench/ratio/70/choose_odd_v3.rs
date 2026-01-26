use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_extend_no_odd_prefix(v: &Vec<u64>, j: usize)
    requires
        j < v.len(),
        forall |q:int| 0 <= q < j ==> #[trigger] v[q] % 2 != 1,
        v[j as int] % 2 != 1,
    ensures
        forall |q:int| 0 <= q < j + 1 ==> #[trigger] v[q] % 2 != 1
{
    assert(forall |q:int| 0 <= q < j + 1 ==> #[trigger] v[q] % 2 != 1) by {
        let qq = arbitrary::<int>();
        if 0 <= qq < j + 1 {
            if qq < j {
                assert(v[qq] % 2 != 1);
            } else {
                assert(qq == j);
                assert(v[j as int] % 2 != 1);
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut j: usize = 0;

    while (j < v.len())
    // Fill in loop invariants here
    {
        if (v[j] % 2 == 1) {
            return j;
        }

        // Fill in a block of assertions here to complete the proof;

        j = j + 1;
    }

    // Fill in a block of assertions here to complete the proof
    j
}

}