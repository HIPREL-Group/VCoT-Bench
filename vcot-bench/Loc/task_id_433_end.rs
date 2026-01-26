use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_forall_extend(arr: &Vec<i32>, number: i32, i: int)
    requires
        0 <= i,
        i < arr.len(),
        forall|k: int| 0 <= k < i ==> number > arr[k],
        number > arr[i],
    ensures
        forall|k: int| 0 <= k < i + 1 ==> number > arr[k],
{
    assert(forall|k: int| 0 <= k < i + 1 ==> number > arr[k]) by {
        assert forall|k: int| 0 <= k < i + 1 implies number > arr[k] by {
            if 0 <= k < i + 1 {
                if k < i {
                    assert(number > arr[k]);
                } else {
                    assert(number > arr[i]);
                }
            }
        }
    }
}

proof fn lemma_not_forall_from_counterexample(arr: &Vec<i32>, number: i32, j: int)
    requires
        0 <= j,
        j < arr.len(),
        !(number > arr[j]),
    ensures
        !(forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
}

#[verifier::exec_allows_no_decreases_clause]
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut i = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> number > arr[k],
    {
        if number <= arr[i] {
            assert(!(forall|j: int| 0 <= j < arr.len() ==> number > arr[j])) by {
                let j: int = i as int;
                assert(!(number > arr[j])) by {
                    assert(number <= arr[(i as int)]);
                }
                lemma_not_forall_from_counterexample(arr, number, j);
            }
            return false;
        }
        assert(number > arr[(i as int)]);

        proof {
            let ii: int = i as int;
            lemma_forall_extend(arr, number, ii);
        }

        i += 1;
    }

    // Fill in a block of assertions here to complete the proof
    true
}

} // verus!