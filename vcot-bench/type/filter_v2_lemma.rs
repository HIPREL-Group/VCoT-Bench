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
        invariant
            0 <= i <= xlen,
            x@.len() == xlen,
            y@ == x@.take((i as int)).filter(|k: u64| k % 3 == 0),
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        proof {
            lemma_seq_take_ascend(x@, (i as int) + 1);

            reveal(Seq::filter);

            assert(x@.take((i as int) + 1).last() == x@[(i as int)]);
            assert(x@.take((i as int) + 1) == x@.take((i as int)).push(x@[(i as int)]));

            lemma_filter_push_cases_u64(x@.take((i as int)), x@[(i as int)]);

            if x@[(i as int)] % 3 == 0 {
                assert(
                    x@.take((i as int) + 1).filter(|k: u64| k % 3 == 0)
                    == x@.take((i as int)).filter(|k: u64| k % 3 == 0).push(x@[(i as int)])
                );
            } else {
                assert(
                    x@.take((i as int) + 1).filter(|k: u64| k % 3 == 0)
                    == x@.take((i as int)).filter(|k: u64| k % 3 == 0)
                );
            }

            assert(
                y@ == x@.take((i as int) + 1).filter(|k: u64| k % 3 == 0)
            );
        }
        i = i + 1;
    }
    proof {
        assert(i == xlen);
        assert((i as int) == x@.len());

        assert(y@ == x@.take((i as int)).filter(|k: u64| k % 3 == 0));
        assert(x@.take((i as int)) == x@);
        assert(y@ == x@.filter(|k: u64| k % 3 == 0));
    }
}

}