use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_consecutive_prefix_extend(arr: &Vec<i32>, index: int)
    requires
        arr.len() > 0,
        0 <= index,
        index < arr.len() - 1,
        forall|k: int| 0 <= k < arr.len() ==> (0 <= #[trigger] arr[k] + 1 < i32::MAX),
        forall|k: int, l: int| (0 <= k < l <= index && l == k + 1) ==> (arr[k] + 1 == arr[l]),
        arr[index] + 1 == arr[index + 1],
    ensures
        forall|k: int, l: int| (0 <= k < l <= index + 1 && l == k + 1) ==> (arr[k] + 1 == arr[l]),
{
    assert(forall|k: int, l: int|
        (0 <= k < l <= index + 1 && l == k + 1) ==> (arr[k] + 1 == arr[l])
    ) by {
        assert forall|k: int, l: int|
            (0 <= k < l <= index + 1 && l == k + 1) implies (arr[k] + 1 == arr[l])
        by {
            if 0 <= k < l <= index + 1 && l == k + 1 {
                if l <= index {
                    assert(0 <= k < l <= index && l == k + 1);
                    assert(arr[k] + 1 == arr[l]);
                } else {
                    assert(l == index + 1) by {
                        assert(l <= index + 1);
                        assert(!(l <= index));
                    }
                    assert(k == index) by {
                        assert(l == k + 1);
                        assert(l == index + 1);
                        assert(k + 1 == index + 1);
                    }
                    assert(arr[k] + 1 == arr[l]);
                }
            }
        }
    }
}

#[verifier::exec_allows_no_decreases_clause]
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while (index < arr.len() - 1)
        // Fill in loop invariants here
    {
        if (arr[index] + 1 != arr[index + 1]) {
            assert(!(forall|i: int, j: int|
                0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])
            )) by {
                let i = index as int;
                let j = i + 1;

                assert(i < arr.len() - 1) by {
                    assert(index < arr.len() - 1);
                }
                assert(j < arr.len()) by {
                    assert(i < arr.len() - 1);
                    assert(j == i + 1);
                }
                assert(!(arr[i] + 1 == arr[j])) by {
                    assert(arr[(index as int)] + 1 != arr[(index as int) + 1]);
                }
            };
            return false;
        }

        proof {
            lemma_consecutive_prefix_extend(arr, (index as int));
        }

        index += 1;
    }

    assert(index == arr.len() - 1) by {
        assert(!(index < arr.len() - 1));
        assert(0 <= index <= arr.len() - 1);
    }

    assert(forall|i: int, j: int|
        0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])
    ) by {
        assert forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 implies (arr[i] + 1 == arr[j])
        by {
            if 0 <= i < j < arr.len() && j == i + 1 {
                assert(j <= index);
                assert(0 <= i < j <= index && j == i + 1);
                assert(arr[i] + 1 == arr[j]);
            }
        }
    };

    true
}

} // verus!