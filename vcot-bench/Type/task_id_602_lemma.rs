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

// Complete the lemma function below
proof fn lemma_drop_last_is_subrange_0_len_minus_1_u8(s: Seq<u8>)
   

// Complete the lemma function below
proof fn lemma_subrange_drop_last_step_u8(s: Seq<u8>, i: int)
   

// Complete the lemma function below
proof fn lemma_count_frequency_rcr_step_append_last_u8(s: Seq<u8>, i: int, key: u8)
   

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

// Complete the lemma function below
proof fn lemma_take_succ_drop_last_u8(s: Seq<u8>, i: int)
   

// Complete the lemma function below
proof fn lemma_filter_ext_eq_implies_all_pred<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    

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
        invariant
            0 <= index <= str1.len(),
            str1@.take((index as int)) =~= str1@.take((index as int)).filter(
                |x: u8| count_frequency_rcr(str1@, x) <= 1,
            ),
    {
        if count_frequency(&str1, str1[index]) > 1 {
            return Some((index, str1[index]));
        }

        assert(str1@.take(((index + 1) as int)).drop_last() == str1@.take((index as int))) by {
            lemma_take_succ_drop_last_u8(str1@, (index as int));
        }

        reveal(Seq::filter);
        index += 1;
    }
    assert(str1@ =~= str1@.take((input_len as int)));
    assert(forall|k: int|
        0 <= k < str1.len() ==> count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1) by {
        let p = |x: u8| count_frequency_rcr(str1@, x) <= 1;

        assert(str1@.take((input_len as int)) =~= str1@.take((input_len as int)).filter(p));
        assert(str1@ =~= str1@.filter(p));

        lemma_filter_ext_eq_implies_all_pred::<u8>(str1@, p);

        assert forall|k: int| 0 <= k < str1.len() implies count_frequency_rcr(str1@, #[trigger] str1[k]) <= 1 by {
            assert(0 <= k < str1@.len());
            assert(p(str1@[k]));
        }
    }
    None
}

}