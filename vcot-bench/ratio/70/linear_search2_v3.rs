use vstd::prelude::*;

fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_forall_prefix_extend<T>(s: Seq<T>, n: int, v: T)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn linear_search(a: &Vec<i32>, e: i32) -> (n: usize)
    requires
        exists|i: int| (0 <= i < a.len() as int) && a[i] == e,
    ensures
        0 <= n < a.len(),
        a[n as int] == e,
        forall|k: int| (0 <= k < n as int) ==> a[k] != e,
{
    let mut n: usize = 0;
    while n != a.len()
        // Fill in loop invariants here
    {
        if a[n] == e {
            return n;
        }

        proof {
            lemma_forall_prefix_extend(a@, n as int, e);

            assert(forall|i: int| (0 <= i < (n + 1) as int) ==> e != a[i]) by {
                assert(forall|i: int| (0 <= i < (n + 1) as int) ==> e != a[i]) by {
                    forall|i: int| (0 <= i < (n + 1) as int) ==> e != a[i] by {
                        if i < n as int {
                            assert(e != a[i]);
                        } else {
                            assert(i == n as int) by {
                                assert(i <= n as int);
                                assert(!(i < n as int));
                            }
                            assert(a[i] == a[n as int]);
                            assert(e != a[n as int]);
                        }
                    }
                }
            }
        }

        n = n + 1;
    }

    // Fill in a block of assertions here to complete the proof

    n
}

} // verus!