use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
   

#[verifier::exec_allows_no_decreases_clause]
fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
    {
        if (str[i] == key) {
            proof {
                assert(exists|j: int| 0 <= j < str.len() && (str[j] == key)) by {
                    assert(0 <= (i as int) && (i as int) < str.len() && str[(i as int)] == key);
                }
            }
            return true;
        }

        proof {
            assert(str[i as int] != key);
        }

        i += 1;

        proof {
            assert forall|m: int| 0 <= m < i implies (str[m] != key) by {
                if m < i - 1 {
                    assert(str[m] != key);
                } else {
                    assert(m == (i - 1) as int);
                    assert(str[(i - 1) as int] != key);
                }
            }
        }
    }

    proof {
        assert(!(exists|j: int| 0 <= j < str.len() && (str[j] == key))) by {
            assert forall|j: int| 0 <= j < str.len() implies (str[j] != key) by {
                assert(str[j] != key);
            }
        }
    }

    false
}

// Complete the lemma function below
proof fn lemma_remove_chars_push_preserves_invariant(
    str1: &[u8],
    str2: &[u8],
    old_out: Seq<u8>,
    old_index: usize,
    new_out: Seq<u8>,
    x: u8,
)
   

// Complete the lemma function below
proof fn lemma_remove_chars_progress_invariant(
    str1: &[u8],
    str2: &[u8],
    out: Seq<u8>,
    old_index: usize,
    new_index: usize,
    processed: u8,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn remove_chars(str1: &[u8], str2: &[u8]) -> (result: Vec<u8>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    let ghost mut output_len: int = 0;

    while index < str1.len()
        invariant
            forall|k: int|
                0 <= k < output_str.len() ==> (str1@.contains(#[trigger] output_str[k])
                    && !str2@.contains(#[trigger] output_str[k])),
            forall|k: int|
                0 <= k < index ==> (str2@.contains(#[trigger] str1[k]) || output_str@.contains(
                    #[trigger] str1[k],
                )),
    {
        if (!contains(str2, str1[index])) {
            proof {
                let old_seq = output_str@;
                let old_len_usize = output_str.len();
                let old_len_int: int = old_len_usize as int;

                lemma_vec_push(old_seq, str1[index as int], old_len_usize);

                assert(forall|k: int|
                    0 <= k < old_seq.len() ==> #[trigger] old_seq[k] == old_seq.push(str1[index as int])[k]
                );

                assert(old_seq.push(str1[index as int]).index(old_len_int) == str1[index as int]);

                assert(str1@.contains(str1[index as int])) by {
                    assert(str1@.index(index as int) == str1[index as int]);
                    assert(str1@.contains(str1@.index(index as int)));
                }

                assert(!str2@.contains(str1[index as int]));

                lemma_remove_chars_push_preserves_invariant(
                    str1,
                    str2,
                    old_seq,
                    index,
                    old_seq.push(str1[index as int]),
                    str1[index as int],
                );

                output_len = output_len + 1;
            }
            output_str.push(str1[index]);
        } else {
            proof {
                assert(str2@.contains(str1[index as int]));
            }
        }
        proof {
            let old_index = index;
            let new_index = old_index + 1;
            let processed = str1[old_index as int];

            assert(str2@.contains(processed) || output_str@.contains(processed)) by {
                if str2@.contains(processed) {
                    assert(str2@.contains(processed));
                } else {
                    assert(output_str@.contains(processed)) by {
                        assert(output_str@.contains(str1[old_index as int]));
                    }
                }
            }

            lemma_remove_chars_progress_invariant(
                str1,
                str2,
                output_str@,
                old_index,
                new_index as usize,
                processed,
            );
        }

        index += 1;
    }
    output_str
}

} // verus!