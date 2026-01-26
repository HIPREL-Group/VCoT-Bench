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

// Complete the lemma function below
proof fn lemma_subrange_drop_last_equiv<A>(s: Seq<A>, i: int)
   

// Complete the lemma function below
proof fn lemma_count_boolean_unfold_nonempty(s: Seq<bool>)
   

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
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_boolean(arr@.subrange(0, (index as int))) == counter,
    {
        if (arr[index]) {
            counter += 1;
        }
        index += 1;

        proof {
            let i: int = (index as int);
            assert(0 <= i);

            assert(i - 1 == ((index - 1) as int)) by {
                assert(index >= 1);
            }

            assert(arr@.subrange(0, ((index - 1) as int)) == arr@.subrange(0, i).drop_last()) by {
                lemma_subrange_drop_last_equiv(arr@, i);
            }

            let prev_i: int = i - 1;
            assert(prev_i < arr@.len()) by {
                assert(i <= arr@.len());
            }

            lemma_subrange_add1_is_drop_last_plus_last(arr@, prev_i);

            assert(arr@.subrange(0, prev_i + 1) == arr@.subrange(0, i));

            assert(
                count_boolean(arr@.subrange(0, i))
                == count_boolean(arr@.subrange(0, prev_i))
                    + (if arr@[prev_i] { 1int } else { 0int })
            );
        }

        assert(arr@.subrange(0, ((index - 1) as int)) == arr@.subrange(0, (index as int)).drop_last()) by {
            lemma_subrange_drop_last_equiv(arr@, (index as int));
        }
    }
    // Fill in a block of assertions here to complete the proof
    counter
}

}