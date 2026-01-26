//This is an example taken from Verus tutorial

use vstd::prelude::*;
fn main() {}

verus!{

pub proof fn lemma_intersect_remove_commutes<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2),
{
    assert forall |x: A| s1.intersect(s2).remove(a).contains(x) == s1.remove(a).intersect(s2).contains(x) by {
        if x == a {
            assert(!s1.intersect(s2).remove(a).contains(x));
            assert(!s1.remove(a).intersect(s2).contains(x));
        } else {
            assert(s1.intersect(s2).remove(a).contains(x) == s1.intersect(s2).contains(x));
            assert(s1.remove(a).intersect(s2).contains(x) == s1.intersect(s2).contains(x));
        }
    }
    assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
}

// Complete the lemma function below
pub proof fn lemma_remove_len_le<A>(s: Set<A>, a: A)
   

#[verifier::exec_allows_no_decreases_clause]
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2).len() == 0) by {
            assert(s1.intersect(s2) =~= s1);
        }
    } else {
        let a = s1.choose();

        assert(s1.contains(a));
        assert(s1.remove(a).finite());

        assert(s1.remove(a).len() < s1.len()) by {
            assert(s1.len() == s1.remove(a).len() + 1) by {
                assert(s1.len() == s1.remove(a).len() + if s1.contains(a) { 1int } else { 0int });
            }
        }

        lemma_len_intersect(s1.remove(a), s2);

        assert(s1.intersect(s2).remove(a).len() <= s1.remove(a).len()) by {
            lemma_intersect_remove_commutes(s1, s2, a);
            assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));

            assert(s1.intersect(s2).remove(a).len() == s1.remove(a).intersect(s2).len());
            assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        }

        lemma_remove_len_le(s1.intersect(s2), a);

        assert(s1.intersect(s2).len() <= s1.len()) by {
            if s1.intersect(s2).contains(a) {
                assert(s1.intersect(s2).len() == s1.intersect(s2).remove(a).len() + 1) by {
                    assert(s1.intersect(s2).len()
                        == s1.intersect(s2).remove(a).len()
                            + if s1.intersect(s2).contains(a) { 1int } else { 0int });
                }
                assert(s1.len() == s1.remove(a).len() + 1) by {
                    assert(s1.len() == s1.remove(a).len() + if s1.contains(a) { 1int } else { 0int });
                }
                assert(s1.intersect(s2).remove(a).len() + 1 <= s1.remove(a).len() + 1);
            } else {
                assert(s1.intersect(s2).remove(a) =~= s1.intersect(s2));
                assert(s1.intersect(s2).len() == s1.intersect(s2).remove(a).len());
            }
            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}