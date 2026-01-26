use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    let sl: int = l as int;

    assert(forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k]) by {
        assert forall|k: int| 0 <= k < vec.len() implies #[trigger] vec[k] == vec.push(i)[k] by {
            assert(vec[k] == vec.index(k));
            assert(vec.push(i)[k] == vec.push(i).index(k));
        }
    };

    assert(vec.push(i).index(sl) == i) by {
        assert(sl == vec.len() as int);
        assert(vec.push(i).index(vec.len() as int) == i);
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        // Fill in loop invariants here
    {
        if (str[i] == key) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }

        proof {
            assert(str[i as int] != key);
        }

        i += 1;

        // Fill in a block of assertions here to complete the proof
    }

    // Fill in a block of assertions here to complete the proof

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
   

proof fn lemma_remove_chars_progress_invariant(
    str1: &[u8],
    str2: &[u8],
    out: Seq<u8>,
    old_index: usize,
    new_index: usize,
    processed: u8,
)
    requires
        new_index == old_index + 1,
        processed == str1[old_index as int],
        forall|k: int|
            0 <= k < old_index ==> (str2@.contains(#[trigger] str1[k]) || out.contains(#[trigger] str1[k])),
        str2@.contains(processed) || out.contains(processed),
    ensures
        forall|k: int|
            0 <= k < new_index ==> (str2@.contains(#[trigger] str1[k]) || out.contains(#[trigger] str1[k])),
{
    assert forall|k: int|
        0 <= k < new_index implies (str2@.contains(#[trigger] str1[k]) || out.contains(#[trigger] str1[k])) by {
        if k < old_index {
            assert(str2@.contains(str1[k]) || out.contains(str1[k]));
        } else {
            assert(k == old_index as int);
            assert(str2@.contains(processed) || out.contains(processed));
        }
    }
}

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
        // Fill in loop invariants here
    {
        if (!contains(str2, str1[index])) {
            // Fill in a block of assertions here to complete the proof
            output_str.push(str1[index]);
        } else {
            // Fill in a block of assertions here to complete the proof
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