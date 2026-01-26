use vstd::prelude::*;
fn main() {}
verus!{

// Complete the lemma function below
proof fn lemma_i32_add_4_no_overflow(v: i32)
   

proof fn lemma_forall_extend_by_one<T>(
    s: Seq<T>,
    i: int,
    p: spec_fn(int) -> bool,
)
    requires
        forall |k:int| 0 <= k < i ==> #[trigger] p(k),
        p(i),
    ensures
        forall |k:int| 0 <= k < i + 1 ==> #[trigger] p(k),
{
    assert forall |k:int| 0 <= k < i + 1 implies #[trigger] p(k) by {
        if k < i {
            assert(p(k));
        } else {
            assert(k == i);
            assert(p(k));
        }
    }
}

proof fn lemma_shift_lower_segment<T>(
    i: int,
    xlen: int,
    p: spec_fn(int) -> bool,
)
    requires
        forall |k:int| i <= k < xlen ==> #[trigger] p(k),
    ensures
        forall |k:int| i + 1 <= k < xlen ==> #[trigger] p(k),
{
    assert forall |k:int| i + 1 <= k < xlen implies #[trigger] p(k) by {
        assert(i <= k);
        assert(p(k));
    }
}

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun2(x: &mut Vec<i32>) 
requires 
    forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
ensures 
    x@.len() == old(x)@.len(),
    forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4,
{
    let mut i: usize = 0;
    let xlen: usize = x.len();

    while (i < xlen) 
        // Fill in loop invariants here
    { 
        let temp = x[i];

        assert(temp == old(x)[(i as int)]) by {
            assert((i as int) < (xlen as int));
        }

        assert(old(x)[(i as int)] <= 0x7FFF_FFFB) by {
            assert((i as int) < (xlen as int));
        }

        proof {
            lemma_i32_add_4_no_overflow(temp);
        }

        x.set(i, temp + 4);

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }  

    assert(x@.len() == old(x)@.len()) by {
        assert(x.len() == xlen);
        assert(old(x).len() == xlen);
    }

    assert(forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4) by {
        assert(forall |k:int| 0 <= k < i ==> #[trigger] x[k] == old(x)[k] + 4);
        assert(i == xlen);
        assert forall |k:int| 0 <= k < x.len() implies #[trigger] x@[k] == old(x)@[k] + 4 by {
            assert(k < (i as int));
        }
    }
}
}