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
    assert(forall|k: int|
        0 <= k < vec.len() ==> vec.push(i).index(k) == vec.index(k)
    ) by {
        assert forall|k: int| 0 <= k < vec.len() implies vec.push(i).index(k) == vec.index(k) by {
            vstd::seq::axiom_seq_push_index_different::<T>(vec, i, k);
        }
    };

    assert(vec.push(i).index(l as int) == i) by {
        vstd::seq::axiom_seq_push_index_same::<T>(vec, i, l as int);
    };
}

proof fn lemma_not_exists_from_forall_prefix<T>(
    s: Seq<T>,
    key: T,
    i: int,
)
    requires
        forall|m: int| 0 <= m < i ==> s[m] != key,
    ensures
        !exists|j: int| 0 <= j < i && s[j] == key,
{
    if exists|j: int| 0 <= j < i && s[j] == key {
        let j = choose|j: int| 0 <= j < i && s[j] == key;
        assert(s[j] != key);
        assert(false);
    }
}

proof fn lemma_exists_from_return_true(
    s: Seq<i32>,
    key: i32,
    i: int,
)
    requires
        0 <= i < s.len(),
        s[i] == key,
    ensures
        exists|j: int| 0 <= j < s.len() && s[j] == key,
{
}

proof fn lemma_forall_prefix_extend_one<T>(
    s: Seq<T>,
    key: T,
    i: int,
)
    requires
        forall|m: int| 0 <= m < i ==> s[m] != key,
        0 <= i < s.len(),
        s[i] != key,
    ensures
        forall|m: int| 0 <= m < i + 1 ==> s[m] != key,
{
    assert forall|m: int| 0 <= m < i + 1 implies s[m] != key by {
        if m < i {
            assert(s[m] != key);
        } else {
            assert(s[m] != key);
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
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
                lemma_exists_from_return_true(str@, key, i as int);
            }
            return true;
        }

        proof {
            lemma_forall_prefix_extend_one(str@, key, i as int);
        }
        i += 1;
    }

    proof {
        lemma_not_exists_from_forall_prefix(str@, key, i as int);
    }
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    let ghost mut output_len: int = 0;

    while index < arr1.len()
        invariant
            forall|k: int|
                0 <= k < output_str.len() ==> (arr1@.contains(#[trigger] output_str[k])
                    && !arr2@.contains(#[trigger] output_str[k])),
            forall|k: int|
                0 <= k < index ==> (arr2@.contains(#[trigger] arr1[k]) || output_str@.contains(
                    #[trigger] arr1[k],
                )),
    {
        if (!contains(arr2, arr1[index])) {
            proof {
                assert(!arr2@.contains(arr1@[index as int]));

                lemma_vec_push(output_str@, arr1@[index as int], output_str.len());

                output_len = output_len + 1;
            }
            let ghost old_output_str = output_str@;
            output_str.push(arr1[index]);
            // Fill in a block of assertions here to complete the proof
        } else {
            // Fill in a block of assertions here to complete the proof
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    output_str
}

} // verus!