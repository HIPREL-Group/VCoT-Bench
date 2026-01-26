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

        assert(c@.len() == old_n + 1) by {
            assert(c@ == old_c_view@.push(sum)) by { }
            assert(old_c_view@.len() == (old_n as int)) by { }
        }

        assert(forall|i: int| (0 <= i && i < old_n) ==> c[i] == a[i] + b[i]) by {
            assert forall|i: int| (0 <= i && i < old_n) implies c[i] == a[i] + b[i] by {
                assert(c@ == old_c_view@.push(sum)) by { }
                assert(old_c_view@[i] == a[i] + b[i]) by {
                    assert((forall|j: int| (0 <= j && j < old_n) ==> old_c_view@[j] == a[j] + b[j]));
                }
                assert(c[i] == a[i] + b[i]);
            }
        }

        assert(c[(old_n as int)] == a[(old_n as int)] + b[(old_n as int)]) by {
            assert(c@ == old_c_view@.push(sum)) by { }
        }

        n = n + 1;

        // Fill in a block of assertions here to complete the proof
    }
    c
}

} // verus!