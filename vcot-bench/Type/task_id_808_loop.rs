use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_split_lt_index_to_lt_index_plus_1(arr: &Vec<i32>, k: i32, index: int)
    requires
        0 <= index,
        index < arr.len(),
        forall|m: int| 0 <= m < index ==> (arr[m] != k),
        arr[index] != k,
    ensures
        forall|m: int| 0 <= m < index + 1 ==> (arr[m] != k),
{
    assert forall|m: int| 0 <= m < index + 1 implies (arr[m] != k) by {
        if m < index {
            assert(arr[m] != k);
        } else {
            assert(m == index);
            assert(arr[m] != k);
        }
    };
}

proof fn lemma_forall_implies_not_exists<T>(p: spec_fn(T) -> bool)
    ensures
        (forall|x: T| !#[trigger] p(x)) ==> !(exists|x: T| #[trigger] p(x)),
{
    if forall|x: T| !#[trigger] p(x) {
        if exists|x: T| #[trigger] p(x) {
            let x = choose|x: T| #[trigger] p(x);
            assert(p(x));
            assert(!p(x));
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        // Fill in loop invariants here
    {
        if (arr[index] == k) {
            assert(exists|i: int| 0 <= i < arr.len() && (arr[i] == k)) by {
                let i: int = (index as int);
                assert(0 <= i < arr.len());
                assert(arr[i] == k);
            };
            return true;
        }
        assert(arr[(index as int)] != k);

        proof {
            lemma_forall_split_lt_index_to_lt_index_plus_1(arr, k, (index as int));
        }

        index += 1;
    }

    assert(!(exists|i: int| 0 <= i < arr.len() && (arr[i] == k))) by {
        assert forall|i: int| 0 <= i < arr.len() implies (arr[i] != k) by {
            assert(0 <= i < (index as int));
            assert(arr[i] != k);
        };

        lemma_forall_implies_not_exists::<int>(|i: int| 0 <= i < arr.len() && arr[i] == k);

        if exists|i: int| 0 <= i < arr.len() && (arr[i] == k) {
            let i = choose|i: int| 0 <= i < arr.len() && (arr[i] == k);
            assert(0 <= i < arr.len() && arr[i] == k);
            assert(arr[i] != k);
        }
    };

    false
}

} // verus!