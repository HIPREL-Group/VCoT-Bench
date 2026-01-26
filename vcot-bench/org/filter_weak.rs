use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_vec_push_preserves_forall_mod3_and_contains(
    x: Seq<u64>,
    y: Seq<u64>,
    v: u64,
)
requires
    forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x.contains(y[k]),
    v % 3 == 0,
    x.contains(v),
ensures
    forall |k:int| 0 <= k < y.push(v).len() ==> y.push(v)[k] % 3 == 0 && x.contains(y.push(v)[k]),
{
    assert forall |k:int| 0 <= k < y.push(v).len() implies y.push(v)[k] % 3 == 0 && x.contains(y.push(v)[k]) by {
        if 0 <= k < y.push(v).len() {
            if k < y.len() {
                assert(y.push(v)[k] == y[k]);
                assert(y[k] % 3 == 0 && x.contains(y[k]));
            } else {
                assert(k == y.len());
                assert(y.push(v)[k] == v);
                assert(v % 3 == 0);
                assert(x.contains(v));
            }
        }
    };
}

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
        invariant 
            x@.len() == xlen,
            forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
    { 
        if (x[i] % 3 == 0) {
            proof {
                let v: u64 = x@[(i as int)];
                assert(v == x@[i as int]);
                assert(x@.contains(v));
                lemma_vec_push_preserves_forall_mod3_and_contains(x@, y@, v);
            }
            y.push(x[i]);
        }
        i = i + 1;
    }
 }
}