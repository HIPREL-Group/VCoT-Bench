use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::exec_allows_no_decreases_clause]
fn copy(a: &Vec<u64>) -> (b: Vec<u64>)
    requires
        a.len() <= 100,
    ensures
        b@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> b[i] == a[i],
{
    let mut b = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();

    // Fill in a block of assertions here to complete the proof;

    while n != len
        invariant
            n <= len,
            n == b@.len(),
            len == a@.len(),
            forall|i: int| (0 <= i && i < n) ==> b[i] == a[i],
    {
        let v = a[n];

        let ghost old_b = b@;
        let old_n = n;

        b.push(v);

        n = n + 1;

        // Fill in a block of assertions here to complete the proof
    }

    assert(b@.len() == a@.len()) by {
        assert(n == b@.len());
        // Fill in a block of assertions here to complete the proof;
        assert(n == len);
    }

    assert forall|i: int| (0 <= i && i < a.len()) implies b[i] == a[i] by {
        // Fill in a block of assertions here to complete the proof;
        assert(n == len);
        assert(i < n);
    }

    b
}

} // verus!