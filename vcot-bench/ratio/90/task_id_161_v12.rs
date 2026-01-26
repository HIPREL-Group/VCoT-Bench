use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
   

// Complete the lemma function below
proof fn lemma_not_exists_from_forall_prefix<T>(
    s: Seq<T>,
    key: T,
    i: int,
)
   

// Complete the lemma function below
proof fn lemma_exists_from_return_true(
    s: Seq<i32>,
    key: i32,
    i: int,
)
   

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
        // Fill in loop invariants here
    {
        if (str[i] == key) {
            // Fill in a block of assertions here to complete the proof
            return true;
        }

        // Fill in a block of assertions here to complete the proof
        i += 1;
    }

    // Fill in a block of assertions here to complete the proof
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
        // Fill in loop invariants here
    {
        if (!contains(arr2, arr1[index])) {
            // Fill in a block of assertions here to complete the proof
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