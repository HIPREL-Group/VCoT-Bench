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
        invariant
            n <= len,
            n == c@.len(),
            len == a@.len(),
            a.len() <= 100 && a.len() == b.len(),
            forall|i: int| (0 <= i && i < a.len()) ==> (a[i] + b[i] < 1000),
            forall|i: int| (0 <= i && i < n) ==> c[i] == #[trigger] a[i] + #[trigger] b[i],
    {
        let sum: u32 = a[n] + b[n];

        let old_n = n;
        let old_c_view = Ghost(c@);

        c.push(sum);

        // Fill in a block of assertions here to complete the proof

        n = n + 1;

        assert(forall|i: int| (0 <= i && i < n) ==> c[i] == a[i] + b[i]) by {
            let nn: int = (n as int);
            let on: int = (old_n as int);
            assert forall|i: int| (0 <= i && i < nn) implies c[i] == a[i] + b[i] by {
                if i < on {
                    assert(c[i] == a[i] + b[i]) by {
                        assert((forall|j: int| (0 <= j && j < old_n) ==> c[j] == a[j] + b[j]));
                    }
                } else {
                    assert(c[i] == a[i] + b[i]) by {
                        assert(c[(old_n as int)] == a[(old_n as int)] + b[(old_n as int)]);
                    }
                }
            }
        }
    }
    c
}

} // verus!