use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_usize_index_swap_preserves_old_prefix<T>(
    length: usize,
    n: usize,
    i: int,
)
   

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    while n < length / 2
        invariant
            0 <= n <= length / 2,
            v.len() == old(v).len(),
            v.len() == length,
            forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1],
            forall|i: int| 0 <= i < n ==> v[length - i - 1] == old(v)[i],
            forall|i: int| n <= i < length - n ==> v[i] == old(v)[i],
        decreases length / 2 - n
    {
        let x = v[n];
        let y = v[length - 1 - n];

        v.set(n, y);
        v.set(length - 1 - n, x);

        assert(forall|i: int| 0 <= i < n ==> v[i] == old(v)[length - i - 1]) by {
            assert forall|i: int| 0 <= i < n implies v[i] == old(v)[length - i - 1] by {
                lemma_usize_index_swap_preserves_old_prefix::<u64>(length, n, i);
            }
        }

        assert(forall|i: int| 0 <= i < n ==> v[length - i - 1] == old(v)[i]) by {
            assert forall|i: int| 0 <= i < n implies v[length - i - 1] == old(v)[i] by {
                lemma_usize_index_swap_preserves_old_prefix::<u64>(length, n, i);
            }
        }

        assert(forall|i: int| n + 1 <= i < length - (n + 1) ==> v[i] == old(v)[i]) by {
            assert forall|i: int| n + 1 <= i < length - (n + 1) implies v[i] == old(v)[i] by {
                assert(n + 1 <= i < length - (n + 1));
                assert(n <= i < length - n);
                assert(v[i] == old(v)[i]);
            }
        }

        n = n + 1;
    }
}
}