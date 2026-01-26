//This is an example taken from Verus tutorial

use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
pub proof fn lemma_intersect_remove_commutes<A>(s1: Set<A>, s2: Set<A>, a: A)
    

// Complete the lemma function below
pub proof fn lemma_remove_len_le<A>(s: Set<A>, a: A)
   

#[verifier::exec_allows_no_decreases_clause]
// Complete the lemma function below
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
   
}