use vstd::prelude::*;

fn main() {}
verus! {

proof fn lemma_forall_extend_a_case(
    a: &Vec<u64>,
    b: &Vec<u64>,
    c: &Vec<u64>,
    n: usize,
    len: usize,
)
    requires
        n < len,
        c@.len() == n + 1,
        len == a@.len() + b@.len(),
        forall|i: int| (0 <= i && i < a.len() && i < n) ==> c[i] == a[i],
        forall|i: int| (a.len() <= i && i < c.len() && i < n) ==> c[i] == b[i - a.len()],
        n < a.len(),
        c[n as int] == a[n as int],
    ensures
        forall|i: int| (0 <= i && i < a.len() && i < n + 1) ==> c[i] == a[i],
{
    assert(forall|i: int| (0 <= i && i < a.len() && i < n + 1) ==> c[i] == a[i]) by {
        assert(c[n as int] == a[n as int]);
    };
}

proof fn lemma_forall_extend_b_case(
    a: &Vec<u64>,
    b: &Vec<u64>,
    c: &Vec<u64>,
    n: usize,
    len: usize,
)
    requires
        n < len,
        c@.len() == n + 1,
        len == a@.len() + b@.len(),
        forall|i: int| (0 <= i && i < a.len() && i < n) ==> c[i] == a[i],
        forall|i: int| (a.len() <= i && i < c.len() && i < n) ==> c[i] == b[i - a.len()],
        a.len() <= n,
        n - a.len() < b.len(),
        c[n as int] == b[(n - a.len()) as int],
    ensures
        forall|i: int| (a.len() <= i && i < c.len() && i < n + 1) ==> c[i] == b[i - a.len()],
{
    assert(forall|i: int| (a.len() <= i && i < c.len() && i < n + 1) ==> c[i] == b[i - a.len()]) by {
        assert(c[n as int] == b[(n - a.len()) as int]);
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
    requires
        a.len() <= 100 && b.len() <= 100,
    ensures
        c@.len() == a@.len() + b@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],
        forall|i: int| (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()],
{
    let mut c = Vec::with_capacity(a.len() + b.len());
    let mut n: usize = 0;
    let len: usize = a.len() + b.len();

    while n != len
        invariant
            n <= len,
            n == c@.len(),
            len == a@.len() + b@.len(),
            forall|i: int| (0 <= i && i < a.len() && i < n) ==> c[i] == a[i],
            forall|i: int| (a.len() <= i && i < c.len() && i < n) ==> c[i] == b[i - a.len()],
    {
        c.push(
            if 0 <= n && n < a.len() {
                a[n]
            } else {
                b[n - a.len()]
            },
        );

        // Fill in a block of assertions here to complete the proof;

        n = n + 1;
    }

    // Fill in a block of assertions here to complete the proof;

    c
}

} // verus!