use vstd::prelude::*;

fn main() {}
verus! {

#[verifier::exec_allows_no_decreases_clause]
fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while n != len
        invariant
            n <= len,
            n == c@.len(),
            len == a@.len(),
            a.len() <= 100 && a.len() == b.len(),
            forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
            forall|i: int| (0 <= i && i < n) ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
    {
        let product: u32 = a[n] * b[n];

        assert(0 <= (n as int) && (n as int) < (a.len() as int));
        assert(a[n as int] * b[n as int] < 1000);

        c.push(product);

        assert(c@.len() == (n as int) + 1);

        proof {
            let old = c@.drop_last();
            let old_n = n;

            assert(c[old.len() as int] == product);

            assert forall|i: int| 0 <= i && i < (old_n as int) + 1 implies c[i] == a[i] * b[i] by {
                if i < (old_n as int) {
                    assert(old[i] == a[i] * b[i]);
                    assert(c[i] == old[i]);
                } else {
                    assert(i == (old_n as int));
                    assert(product == a[old_n as int] * b[old_n as int]);
                }
            }
        }

        n = n + 1;
    }
    c
}

} // verus!