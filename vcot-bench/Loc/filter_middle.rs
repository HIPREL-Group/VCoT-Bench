use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_filter_take_step_u64(s: Seq<u64>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        s.take(i + 1).filter(|k:u64| k % 3 == 0)
        ==
        if s[i] % 3 == 0 {
            s.take(i).filter(|k:u64| k % 3 == 0).push(s[i])
        } else {
            s.take(i).filter(|k:u64| k % 3 == 0)
        },
{
    reveal(Seq::filter);

    assert(s.take(i + 1).last() == s[i]) by {
        assert(s.take(i + 1)[i] == s[i]);
        assert(s.take(i + 1).last() == s.take(i + 1)[i]);
    }
    
    assert(s.take(i + 1).drop_last() == s.take(i));

    assert(
        s.take(i + 1).filter(|k:u64| k % 3 == 0)
        ==
        if s[i] % 3 == 0 {
            s.take(i).filter(|k:u64| k % 3 == 0).push(s[i])
        } else {
            s.take(i).filter(|k:u64| k % 3 == 0)
        }
    );
}

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

            // Fill in a block of assertions here to complete the proof;
        } else {
            // Fill in a block of assertions here to complete the proof;
        }

        // Fill in a block of assertions here to complete the proof
        i = i + 1;

        assert(y@ == x@.take((i as int)).filter(|k:u64| k%3 == 0));
    }
    assert(x@ == x@.take((x.len() as int)));
    assert(y@ == x@.take((x.len() as int)).filter(|k:u64| k%3 == 0)) by {
        assert(i == xlen);
        assert(y@ == x@.take((i as int)).filter(|k:u64| k%3 == 0));
    };
}
}