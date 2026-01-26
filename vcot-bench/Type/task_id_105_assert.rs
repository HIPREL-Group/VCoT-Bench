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

proof fn lemma_count_boolean_unfold_nonempty(s: Seq<bool>)
    requires
        s.len() > 0,
    ensures
        count_boolean(s) == count_boolean(s.drop_last()) + (if s.last() { 1int } else { 0int }),
{
    assert(s.len() != 0);
    assert(count_boolean(s)
        == count_boolean(s.drop_last()) + if s.last() { 1int } else { 0int });
}

proof fn lemma_subrange_add1_is_drop_last_plus_last(s: Seq<bool>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        count_boolean(s.subrange(0, i + 1))
            == count_boolean(s.subrange(0, i))
                + (if s[i] { 1int } else { 0int }),
{
    let t = s.subrange(0, i + 1);
    assert(t.len() == i + 1) by {
        assert(0 <= i + 1);
        assert(i + 1 <= s.len());
    }
    assert(t.len() > 0);

    lemma_count_boolean_unfold_nonempty(t);

    assert(t.drop_last() == s.subrange(0, i)) by {
        lemma_subrange_drop_last_equiv(s, i + 1);
    }

    assert(t.last() == s[i]) by {
        assert(t.last() == t[t.len() - 1]);
        assert(t.len() - 1 == i);
        assert(t[i] == s[i]);
    }

    assert(count_boolean(t) == count_boolean(s.subrange(0, i)) + (if s[i] { 1int } else { 0int }));
}

proof fn lemma_subrange_len_when_in_bounds_bool(s: Seq<bool>, i: int)
    requires
        0 <= i,
        i <= s.len(),
    ensures
        s.subrange(0, i).len() == i,
{
    assert(s.subrange(0, i).len() == i) by {
        assert(0 <= i);
        assert(i <= s.len());
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn count_true(arr: &Vec<bool>) -> (count: u64)
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
{
    let mut index = 0;
    let mut counter = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_boolean(arr@.subrange(0, (index as int))) == counter,
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    // Fill in a block of assertions here to complete the proof
    counter
}

}