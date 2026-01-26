use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_push_cases_u64(s: Seq<u64>, a: u64)
    

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires
    old(y).len() == 0,
ensures
    y@ == x@.filter(|k: u64| k % 3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();

    assert(y@ == x@.take(0).filter(|k: u64| k % 3 == 0));
    while (i < xlen)
        // Fill in loop invariants here
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        // Fill in a block of assertions here to complete the proof
        i = i + 1;
    }
    // Fill in a block of assertions here to complete the proof
}

}