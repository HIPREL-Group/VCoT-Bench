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

        assert(c@ == old_c.push(v[n as int]));

        assert(c@.len() == (n as int) + 1);
        assert(forall|i: int| 0 <= i < old_n ==> c[i] == v[i]) by {
            assert forall|i: int| 0 <= i < old_n implies c[i] == v[i] by {
                assert(c[i] == old_c.push(v[n as int])[i]);
                assert(old_c.push(v[n as int])[i] == old_c[i]);
            };
        };

        assert(c[old_n] == v[old_n]) by {
            assert(c[old_n] == old_c.push(v[n as int])[old_n]);
            assert(old_c.push(v[n as int])[old_n] == v[n as int]);
            assert(v[n as int] == v[old_n]);
        };

        n = n + 1;

        assert(forall|i: int| 0 <= i < n ==> c[i] == v[i]) by {
            assert(forall|i: int| 0 <= i < old_n ==> c[i] == v[i]);
            assert(c[old_n] == v[old_n]);
        };
    }

    // Fill in a block of assertions here to complete the proof;

    let ghost old_c = c@;
    c.push(elem);

    // Fill in a block of assertions here to complete the proof;

    c
}

} // verus!