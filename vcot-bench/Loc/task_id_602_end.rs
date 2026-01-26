use vstd::prelude::*;

fn main() {
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<u8>, key: u8) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            (1 as int)
        } else {
            (0 as int)
        }
    }
}

proof fn lemma_drop_last_is_subrange_0_len_minus_1_u8(s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        s.drop_last() == s.subrange(0, s.len() - 1),
{
}

proof fn lemma_subrange_drop_last_step_u8(s: Seq<u8>, i: int)
    requires
        0 < i <= s.len(),
    ensures
        s.subrange(0, i - 1) == s.subrange(0, i).drop_last(),
{
    let t = s.subrange(0, i);

    assert(t.len() == i) by {
        if i <= s.len() {
            assert(t.len() == i);
        }
    }

    assert(t.len() > 0) by { assert(t.len() == i); }

    lemma_drop_last_is_subrange_0_len_minus_1_u8(t);
    assert(t.drop_last() == t.subrange(0, t.len() - 1));
    assert(t.len() - 1 == i - 1) by { assert(t.len() == i); }

    assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1)) by {
        if i <= s.len() {
            assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1));
        } else {
            assert(true);
        }
    }

    assert(s.subrange(0, i).drop_last() == s.subrange(0, i - 1)) by {
        assert(t == s.subrange(0, i));
        assert(t.drop_last() == t.subrange(0, t.len() - 1));
        assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1));
    }
}

proof fn lemma_count_frequency_rcr_step_append_last_u8(s: Seq<u8>, i: int, key: u8)
    requires
        0 < i <= s.len(),
    ensures
        count_frequency_rcr(s.subrange(0, i), key)
            == count_frequency_rcr(s.subrange(0, i - 1), key)
                + (if s[i - 1] == key { 1int } else { 0int }),
{
    let t = s.subrange(0, i);

    assert(t.len() == i) by { if i <= s.len() { assert(t.len() == i); } }

    assert(t.len() > 0) by { assert(t.len() == i); }

    lemma_drop_last_is_subrange_0_len_minus_1_u8(t);
    assert(t.drop_last() == t.subrange(0, t.len() - 1));
    assert(t.len() - 1 == i - 1) by { assert(t.len() == i); }

    assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1)) by {
        if i <= s.len() {
            assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1));
        } else {
            assert(true);
        }
    }

    assert(t.last() == s[i - 1]) by {
        assert(t.len() == i);
        assert(t.len() - 1 == i - 1);
        assert(t.last() == t[t.len() - 1]);
        assert(t[t.len() - 1] == t[i - 1]) by { assert(t.len() - 1 == i - 1); }
        assert(t[i - 1] == s[i - 1]) by {
            if i <= s.len() {
                assert(0 <= i - 1 < i);
            }
        }
    }

    assert(
        count_frequency_rcr(t, key)
            == count_frequency_rcr(t.drop_last(), key)
                + (if t.last() == key { 1int } else { 0int })
    );

    assert(t.drop_last() == s.subrange(0, i - 1)) by {
        assert(t.drop_last() == t.subrange(0, t.len() - 1));
        assert(t.subrange(0, t.len() - 1) == s.subrange(0, i - 1));
    }

    assert(
        count_frequency_rcr(s.subrange(0, i), key)
            == count_frequency_rcr(s.subrange(0, i - 1), key)
                + (if s[i - 1] == key { 1int } else { 0int })
    ) by {
        assert(t == s.subrange(0, i));
        assert(t.last() == s[i - 1]);
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn count_frequency(arr: &[u8], key: u8) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, (index as int)), key) == counter,
    {
        if (arr[index] == key) {
            counter += 1;
        }

        let old_index = index;
        let old_counter = counter;

        index += 1;

        assert(arr@.subrange(0, ((index - 1) as int)) == arr@.subrange(0, (index as int)).drop_last()) by {
            lemma_subrange_drop_last_step_u8(arr@, (index as int));
        }

        assert(
            count_frequency_rcr(arr@.subrange(0, (index as int)), key)
                == count_frequency_rcr(arr@.subrange(0, (old_index as int)), key)
                    + (if arr@[(old_index as int)] == key { 1int } else { 0int })
        ) by {
            lemma_count_frequency_rcr_step_append_last_u8(arr@, (index as int), key);
            assert(arr@[(old_index as int)] == arr[(old_index as int)]);
        }

        if arr[old_index] == key {
            assert(count_frequency_rcr(arr@.subrange(0, (old_index as int)), key) == old_counter - 1);
            assert(count_frequency_rcr(arr@.subrange(0, (index as int)), key) == counter) by {
                assert(
                    count_frequency_rcr(arr@.subrange(0, (index as int)), key)
                        == count_frequency_rcr(arr@.subrange(0, (old_index as int)), key)
                            + (if arr@[(old_index as int)] == key { 1int } else { 0int })
                );
            }
        } else {
            assert(counter == old_counter);
            assert(
                old_counter
                    == old_counter
                        + (if arr@[(old_index as int)] == key { 1int } else { 0int })
            ) by {
                assert(arr@[(old_index as int)] != key);
            }
            assert(count_frequency_rcr(arr@.subrange(0, (old_index as int)), key) == old_counter);
            assert(count_frequency_rcr(arr@.subrange(0, (index as int)), key) == counter) by {
                assert(
                    count_frequency_rcr(arr@.subrange(0, (index as int)), key)
                        == count_frequency_rcr(arr@.subrange(0, (old_index as int)), key)
                            + (if arr@[(old_index as int)] == key { 1int } else { 0int })
                );
            }
        }

        assert(counter <= index) by {
            if arr[(old_index as int)] == key {
                assert((old_counter as int) - 1 <= (old_index as int));
                assert(counter == old_counter);
                assert(index == old_index + 1);
                assert(counter <= index);
            } else {
                assert(counter == old_counter);
                assert(old_counter <= old_index);
                assert(index == old_index + 1);
                assert(counter <= index);
            }
        }
    }
    assert(arr@ == arr@.subrange(0, (index as int))) by {
        assert(index == arr.len());
        assert(arr@.subrange(0, (index as int)) == arr@);
    }
    counter
}

proof fn lemma_take_succ_drop_last_u8(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.take(((i + 1) as int)).drop_last() == s.take(i),
{
    let j = i + 1;

    assert(s.subrange(0, i) == s.subrange(0, j).drop_last()) by {
        lemma_subrange_drop_last_step_u8(s, j);
    }

    assert(s.take(j).drop_last() == s.take(i)) by {
        assert(s.take(j).drop_last() == s.subrange(0, j).drop_last());
        assert(s.subrange(0, j).drop_last() == s.subrange(0, i));
        assert(s.subrange(0, i) == s.take(i));
    }
}

proof fn lemma_filter_ext_eq_implies_all_pred<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    ensures
        s =~= s.filter(p) ==> forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i]),
{
    reveal(Seq::filter);

    if s =~= s.filter(p) {
        assert(forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i])) by {
            assert forall|i: int| 0 <= i < s.len() implies p(#[trigger] s[i]) by {
                let t = s.filter(p);

                if p(s[i]) {
                } else {
                    assert(false) by {
                        assert(i < t.len() || t.len() <= i);
                        if i < t.len() {
                            assert(s[i] == t[i]);
                            assert(p(t[i]));
                        } else {
                            assert(i < s.len());
                        }
                    }
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn first_repeated_char(str1: &[u8]) -> (repeated_char: Option<(usize, u8)>)
    ensures
        if let Some((idx, rp_char)) = repeated_char {
            &&& str1@.take((idx as int)) =~= str1@.take((idx as int)).filter(
                |x: u8| count_frequency_rcr(str1@, x) <= 1,
            )
            &&& count_frequency_rcr(str1@, rp_char) > 1
        } else {
            forall|k: int|
                0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1
        },
{
    let input_len = str1.len();
    assert(str1@.take(0int).filter(|x: u8| count_frequency_rcr(str1@, x) > 1) == Seq::<
        u8,
    >::empty());
    let mut index = 0;
    while index < str1.len()
        // Fill in loop invariants here
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }

        // Fill in a block of assertions here to complete the proof

        reveal(Seq::filter);
        index += 1;
    }
    // Fill in a block of assertions here to complete the proof
    None
}

}