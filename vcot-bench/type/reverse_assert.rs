use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_usize_index_swap_preserves_old_prefix<T>(
    length: usize,
    n: usize,
    i: int,
)
    requires
        n < length / 2,
        0 <= i < n,
    ensures
        i != n as int
        && i != (length - 1 - n) as int
        && (length - 1 - i as usize) != n
        && (length - 1 - i as usize) != (length - 1 - n),
{
}

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

        // Fill in a block of assertions here to complete the proof

        n = n + 1;
    }
}
}