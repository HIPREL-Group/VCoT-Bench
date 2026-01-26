use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_forall_prefix_extend<T>(s: Seq<T>, n: int, v: T)
    requires
        0 <= n,
        forall|i: int| 0 <= i < n ==> s[i] != v,
    ensures
        forall|i: int| 0 <= i < n + 1 ==> (if i < n { s[i] != v } else { true }),
{
    assert(forall|i: int| 0 <= i < n + 1 ==> (if i < n { s[i] != v } else { true })) by {
        assert(forall|i: int| 0 <= i < n + 1 ==> (if i < n { s[i] != v } else { true })) by {
            forall|i: int| 0 <= i < n + 1 ==> (if i < n { s[i] != v } else { true }) by {
                if i < n {
                    assert(s[i] != v);
                } else {
                }
            }
        }
    }
}

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
        invariant
            n <= a.len(),
            forall|i: int| (0 <= i < n as int) ==> e != a[i],
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

    assert(false) by {
        let i = choose|i: int| (0 <= i < a.len() as int) && a[i] == e;
        assert(a[i] != e);
    }

    n
}

} // verus!