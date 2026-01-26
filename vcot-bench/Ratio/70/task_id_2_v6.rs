use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_forall_prefix_preserved<T>(
    s: Seq<T>,
    key: T,
    i: int,
    j: int,
)
   

proof fn lemma_forall_prefix_extend<T>(
    s: Seq<T>,
    key: T,
    i: int,
)
    requires
        0 <= i,
        forall|m: int| 0 <= m < i ==> s[m] != key,
        s[i] != key,
    ensures
        forall|m: int| 0 <= m < i + 1 ==> s[m] != key,
{
    assert forall|m: int| 0 <= m < i + 1 implies s[m] != key by {
        if m < i {
            assert(s[m] != key);
        } else {
            assert(m == i) by {
                assert(m < i + 1);
                assert(!(m < i));
            };
            assert(s[m] != key);
        }
    }
}

// Complete the lemma function below
proof fn lemma_seq_contains_from_exec_contains(arr: &Vec<i32>, key: i32)
    

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        // Fill in loop invariants here
    {
        if (arr[i] == key) {
            return true;
        }
        // Fill in a block of assertions here to complete the proof
        i += 1;
    }
    proof {
        assert forall|k: int| 0 <= k < arr.len() implies arr[k] != key by {
            assert(0 <= k < i as int) by {
                assert(k < arr.len());
            }
            assert(arr[k] != key);
        }

        assert(!(exists|k: int| 0 <= k < arr.len() && arr[k] == key)) by {
            assert forall|k: int| 0 <= k < arr.len() implies arr[k] != key by {
                assert(0 <= k < i as int);
                assert(arr[k] != key);
            }
        }
    }
    false
}

#[verifier::exec_allows_no_decreases_clause]
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let ghost mut shared_arr_len: int = 0;

    let mut index = 0;
    while index < list1.len()
        // Fill in loop invariants here
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            proof {
                let v = list1@[(index as int)];
                let old_len = shared.len();
                assert(!shared@.contains(v));

                assert(forall|i: int| 0 <= i < old_len ==> (list1@.contains(shared[i]) && list2@.contains(shared[i])));
                assert(forall|m: int, n: int| 0 <= m < n < old_len ==> shared[m] != shared[n]);

                lemma_seq_contains_from_exec_contains(list2, v);
                lemma_seq_contains_from_exec_contains(&shared, v);
            }

            shared.push(list1[index]);

            // Fill in a block of assertions here to complete the proof
        }
        index += 1
    }
    shared
}

}