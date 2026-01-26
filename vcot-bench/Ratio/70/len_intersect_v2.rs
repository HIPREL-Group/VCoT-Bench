//This is an example taken from Verus tutorial

use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
pub proof fn lemma_intersect_remove_commutes<A>(s1: Set<A>, s2: Set<A>, a: A)
    

pub proof fn lemma_remove_len_le<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.remove(a).len() <= s.len(),
{
    if s.contains(a) {
        assert(s.remove(a).len() + 1 == s.len()) by {
            assert(s.len() == s.remove(a).len() + if s.contains(a) { 1int } else { 0int });
        }
    } else {
        assert(s.remove(a) =~= s);
    }
}

#[verifier::exec_allows_no_decreases_clause]
// Complete the lemma function below
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
   
}