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
        // Fill in loop invariants here
        decreases length / 2 - n
    {
        let x = v[n];
        let y = v[length - 1 - n];

        v.set(n, y);
        v.set(length - 1 - n, x);

        // Fill in a block of assertions here to complete the proof

        n = n + 1;
    }
}
}