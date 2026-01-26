use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_filter_take_step_u64(s: Seq<u64>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    assert(y@ == x@.take(0).filter(|k:u64| k%3 ==0));
    while (i < xlen) 
        invariant 
            0 <= i <= xlen,
            x@.len() == xlen,
            y@ == x@.take((i as int)).filter(|k:u64| k%3 == 0),
    { 
        if (x[i] % 3 == 0) {
            let ghost y_before = y@;

            y.push(x[i]);

            assert(y@ == y_before.push(x[(i as int)]));

            proof {
                lemma_filter_take_step_u64(x@, (i as int));
            }
            assert(
                x@.take((i as int) + 1).filter(|k:u64| k%3 == 0)
                ==
                x@.take((i as int)).filter(|k:u64| k%3 == 0).push(x[(i as int)])
            );

            assert(
                y@ == x@.take((i as int) + 1).filter(|k:u64| k%3 == 0)
            ) by {
                assert(y@ == y_before.push(x[(i as int)]));
            };
        } else {
            // Fill in a block of assertions here to complete the proof;
        }

        assert((i + 1) <= xlen);

        proof {
            reveal(Seq::filter);
        }
        i = i + 1;

        // Fill in a block of assertions here to complete the proof;
    }
    assert(x@ == x@.take((x.len() as int)));
    assert(y@ == x@.take((x.len() as int)).filter(|k:u64| k%3 == 0)) by {
        assert(i == xlen);
        // Fill in a block of assertions here to complete the proof;
    };
}
}