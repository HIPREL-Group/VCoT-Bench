use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::exec_allows_no_decreases_clause]
fn sum(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] + b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] + #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();

    while n != len
        // Fill in loop invariants here
    {
        let sum: u32 = a[n] + b[n];

        let old_n = n;
        let old_c_view = Ghost(c@);

        c.push(sum);

        // Fill in a block of assertions here to complete the proof

        n = n + 1;

        // Fill in a block of assertions here to complete the proof
    }
    c
}

} // verus!