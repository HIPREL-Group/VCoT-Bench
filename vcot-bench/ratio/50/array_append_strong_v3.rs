use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::exec_allows_no_decreases_clause]
fn append(v: &Vec<u64>, elem: u64) -> (c: Vec<u64>)
    requires
        v.len() <= 100,
    ensures
        c@.len() == v@.len() + 1,
        forall|i: int| (0 <= i && i < v.len()) ==> c[i] == v[i],
        c@.last() == elem,
{
    let mut c = Vec::with_capacity(v.len() + 1);
    let mut n: usize = 0;
    let len: usize = v.len();

    assert(len == v@.len());

    while n != len
        invariant
            n <= len,
            n == c@.len(),
            len == v@.len(),
            forall|i: int| 0 <= i < n ==> c[i] == v[i],
    {
        let ghost old_c = c@;
        let ghost old_n: int = n as int;

        c.push(v[n]);

        // Fill in a block of assertions here to complete the proof;

        n = n + 1;

        // Fill in a block of assertions here to complete the proof;
    }

    assert(forall|i: int| 0 <= i < v.len() ==> c[i] == v[i]) by {
        assert(forall|i: int| 0 <= i < n ==> c[i] == v[i]);
    };

    let ghost old_c = c@;
    c.push(elem);

    // Fill in a block of assertions here to complete the proof;

    c
}

} // verus!