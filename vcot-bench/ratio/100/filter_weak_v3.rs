use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_vec_push_preserves_forall_mod3_and_contains(
    x: Seq<u64>,
    y: Seq<u64>,
    v: u64,
)

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while (i < xlen) 
        // Fill in loop invariants here
    { 
        if (x[i] % 3 == 0) {
            // Fill in a block of assertions here to complete the proof
            y.push(x[i]);
        }
        i = i + 1;
    }
 }
}