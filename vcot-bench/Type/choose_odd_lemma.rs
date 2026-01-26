use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_extend_no_odd_prefix(v: &Vec<u64>, j: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut j: usize = 0;

    while (j < v.len())
    invariant
        j <= v.len(),
        forall |q:int| 0 <= q < j ==> #[trigger] v[q] % 2 != 1,
    {
        if (v[j] % 2 == 1) {
            return j;
        }

        assert(forall |q:int| 0 <= q < j + 1 ==> #[trigger] v[q] % 2 != 1) by {
            lemma_extend_no_odd_prefix(v, j);
        };

        j = j + 1;
    }

    proof {
        let q = choose |q:int| 0 <= q < v.len() && v[q] % 2 == 1;
        assert(q < j);
        assert(v[q] % 2 != 1);
        assert(v[q] % 2 == 1);
    }
    j
}

}