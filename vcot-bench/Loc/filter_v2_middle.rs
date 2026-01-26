use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0 < i <= v.len(),
    ensures
        v.take(i).drop_last() == v.take(i - 1),
{
    let s_i = v.take(i);
    let s_im1 = v.take(i - 1);

    assert(s_i.len() == i);
    assert(s_im1.len() == i - 1);

    assert(s_i.drop_last().len() == s_i.len() - 1);

    assert(s_i.drop_last().len() == s_im1.len());

    assert forall|j: int|
        0 <= j < s_i.drop_last().len()
        implies s_i.drop_last()[j] == s_im1[j]
    by {
        assert(j < s_im1.len());

        assert(j + 1 <= s_i.len());
        assert(j + 1 <= i);

        assert(s_i.drop_last()[j] == s_i[j]);
        assert(s_i[j] == v[j]);
        assert(s_im1[j] == v[j]);

        assert(s_i.drop_last()[j] == s_im1[j]);
    }

    assert(s_i.drop_last() == s_im1);
}

proof fn lemma_filter_push_cases_u64(s: Seq<u64>, a: u64)
    ensures
        (a % 3 == 0 ==> s.push(a).filter(|k: u64| k % 3 == 0) == s.filter(|k: u64| k % 3 == 0).push(a))
        && (a % 3 != 0 ==> s.push(a).filter(|k: u64| k % 3 == 0) == s.filter(|k: u64| k % 3 == 0)),
{
    reveal(Seq::filter);

    let s_prime = s.push(a);
    assert(s_prime.len() > 0);
    assert(s_prime.drop_last() == s);
    assert(s_prime.last() == a);
}

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
    proof {
        assert(i == xlen);
        assert((i as int) == x@.len());

        assert(y@ == x@.take((i as int)).filter(|k: u64| k % 3 == 0));
        assert(x@.take((i as int)) == x@);
        assert(y@ == x@.filter(|k: u64| k % 3 == 0));
    }
}

}