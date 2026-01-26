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

    assert(c@ == old_c.push(elem));
    assert(c@.len() == old_c.len() + 1);
    assert(c@.len() == v@.len() + 1) by {
        assert(old_c.len() == v@.len());
    };

    assert(c@.last() == elem);

    assert(forall|i: int| (0 <= i && i < v.len()) ==> c[i] == v[i]) by {
        assert forall|i: int| 0 <= i < v.len() implies c[i] == v[i] by {
            assert(c[i] == old_c.push(elem)[i]);
            assert(old_c.push(elem)[i] == old_c[i]);
            assert(old_c[i] == v[i]);
        };
    };

    c
}

} // verus!