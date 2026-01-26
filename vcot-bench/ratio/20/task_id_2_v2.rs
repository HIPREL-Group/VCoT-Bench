use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_prefix_preserved<T>(
    s: Seq<T>,
    key: T,
    i: int,
    j: int,
)
    requires
        0 <= i <= j,
        forall|m: int| 0 <= m < j ==> s[m] != key,
    ensures
        forall|m: int| 0 <= m < i ==> s[m] != key,
{
    assert forall|m: int| 0 <= m < i implies s[m] != key by {
        assert(0 <= m < j) by {
            assert(m < i);
            assert(i <= j);
        }
    }
}

// Complete the lemma function below
proof fn lemma_forall_prefix_extend<T>(
    s: Seq<T>,
    key: T,
    i: int,
)
   

proof fn lemma_seq_contains_from_exec_contains(arr: &Vec<i32>, key: i32)
    ensures
        (exists|i: int| 0 <= i < arr.len() && arr[i] == key) <==> arr@.contains(key),
{
    if exists|i: int| 0 <= i < arr.len() && arr[i] == key {
        assert(arr@.contains(key)) by {
            let w = choose|i: int| 0 <= i < arr.len() && arr[i] == key;
            assert(0 <= w < arr.len());
            assert(arr[w] == key);
        }
    } else {
        assert(!arr@.contains(key)) by {
            assert forall|i: int| 0 <= i < arr.len() implies arr[i] != key by {
                if arr[i] == key {
                    assert(exists|j: int| 0 <= j < arr.len() && arr[j] == key) by {
                        assert(0 <= i < arr.len());
                    }
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
        if (arr[i] == key) {
            return true;
        }
        proof {
            let si = i as int;
            assert(forall|m: int| 0 <= m < si + 1 ==> arr[m] != key) by {
                lemma_forall_prefix_extend(arr@, key, si);
            }
        }
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
        invariant
            forall|i: int|
                0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                    #[trigger] shared[i],
                )),
            forall|m: int, n: int| 0 <= m < n < shared.len() ==> shared[m] != shared[n],
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            // Fill in a block of assertions here to complete the proof

            shared.push(list1[index]);

            proof {
                shared_arr_len = shared_arr_len + 1;

                let v = list1@[(index as int)];
                let old_len = shared.len() - 1;
                let new_len = shared.len();

                assert(new_len == old_len + 1);

                assert forall|i: int| 0 <= i < new_len implies (list1@.contains(shared[i]) && list2@.contains(shared[i])) by {
                    if i < (new_len - 1) {
                        assert(i < old_len) by {
                            assert(new_len == old_len + 1);
                        }
                    } else {
                        assert(i == new_len - 1) by {
                            assert(i < new_len);
                            assert(!(i < new_len - 1));
                        }
                        assert(shared[i] == v);
                        assert(list1@.contains(v));
                        assert(list2@.contains(v));
                    }
                }

                assert forall|m: int, n: int| 0 <= m < n < new_len implies shared[m] != shared[n] by {
                    if n < new_len - 1 {
                        assert(n < old_len) by {
                            assert(new_len == old_len + 1);
                        }
                        assert(m < old_len) by {
                            assert(m < n);
                        }
                    } else {
                        assert(n == new_len - 1) by {
                            assert(n < new_len);
                            assert(!(n < new_len - 1));
                        }
                        assert(m < old_len) by {
                            assert(new_len == old_len + 1);
                        }
                        assert(shared[n] == v);

                        assert(shared[m] != v) by {
                            assert(!shared@.drop_last().contains(v)) by { }
                        }
                    }
                }
            }
        }
        index += 1
    }
    shared
}

}