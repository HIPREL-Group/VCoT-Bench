use vstd::prelude::*;

fn main() {
}

verus! {

spec fn count_boolean(seq: Seq<bool>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            (1 as int)
        } else {
            (0 as int)
        }
    }
}

proof fn lemma_subrange_drop_last_equiv<A>(s: Seq<A>, i: int)
    requires
        0 < i <= s.len(),
    ensures
        s.subrange(0, i).drop_last() == s.subrange(0, i - 1),
{
    let t = s.subrange(0, i);
    assert(t.len() == i);

    let lhs = t.drop_last();
    let rhs = s.subrange(0, i - 1);

    assert(lhs.len() == i - 1);
    assert(rhs.len() == i - 1);

    assert forall |k: int| 0 <= k < i - 1 implies lhs[k] == rhs[k] by {
        assert(lhs[k] == t[k]);
        assert(t[k] == s[k]);
        assert(rhs[k] == s[k]);
    }

    assert(lhs == rhs);
}

// Complete the lemma function below
proof fn lemma_count_boolean_unfold_nonempty(s: Seq<bool>)
   

// Complete the lemma function below
proof fn lemma_subrange_add1_is_drop_last_plus_last(s: Seq<bool>, i: int)
   

// Complete the lemma function below
proof fn lemma_subrange_len_when_in_bounds_bool(s: Seq<bool>, i: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;

    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    assert(arr@ == arr@.subrange(0, (index as int))) by {
        assert(arr@.subrange(0, (arr@.len() as int)) == arr@);
    }
    counter
}

}