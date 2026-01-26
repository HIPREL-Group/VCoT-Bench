use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_min_second_invariant_preserved(
    arr: &Vec<Vec<i32>>,
    min_second_index: int,
    index: int,
    new_min_second_index: int,
)
    requires
        arr.len() > 0,
        0 <= min_second_index < arr.len(),
        0 <= index < arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
        forall|k: int| 0 <= k < index ==> (arr[min_second_index][1] <= #[trigger] arr[k][1]),
        new_min_second_index == (if arr[index][1] < arr[min_second_index][1] { index } else { min_second_index }),
    ensures
        0 <= new_min_second_index < arr.len(),
        forall|k: int| 0 <= k < index + 1 ==> (arr[new_min_second_index][1] <= #[trigger] arr[k][1]),
{
    assert(0 <= new_min_second_index < arr.len()) by {
        if arr[index][1] < arr[min_second_index][1] {
            assert(new_min_second_index == index);
        } else {
            assert(new_min_second_index == min_second_index);
        }
    };

    assert(forall|k: int| 0 <= k < index + 1 ==> (arr[new_min_second_index][1] <= #[trigger] arr[k][1])) by {
        let k = arbitrary::<int>();
        if 0 <= k && k < index + 1 {
            if k == index {
                if arr[index][1] < arr[min_second_index][1] {
                    assert(new_min_second_index == index);
                } else {
                    assert(new_min_second_index == min_second_index);
                    assert(arr[min_second_index][1] <= arr[index][1]) by {
                        assert(!(arr[index][1] < arr[min_second_index][1]));
                    };
                }
            } else {
                if arr[index][1] < arr[min_second_index][1] {
                    assert(new_min_second_index == index);
                    assert(arr[min_second_index][1] <= #[trigger] arr[k][1]) by {
                        assert(0 <= k < index);
                    };
                    assert(arr[index][1] <= arr[min_second_index][1]) by {
                        assert(arr[index][1] < arr[min_second_index][1]);
                    };
                    assert(arr[index][1] <= arr[k][1]) by {
                        assert(arr[index][1] <= arr[min_second_index][1]);
                        assert(arr[min_second_index][1] <= arr[k][1]);
                    };
                } else {
                    assert(new_min_second_index == min_second_index);
                    assert(arr[min_second_index][1] <= arr[k][1]) by {
                        assert(0 <= k < index);
                    };
                }
            }
        }
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
{
    let mut min_second_index = 0;
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= min_second_index < arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,
            forall|k: int|
                0 <= k < (index as int) ==> (arr[(min_second_index as int)][1] <= #[trigger] arr[k][1]),
    {
        assert(arr[(index as int)].len() > 0);
        assert(arr[(min_second_index as int)].len() > 0);

        assert(arr[(index as int)].len() >= 2) by {
            assert(0 <= (index as int) < (arr.len() as int));
        };
        assert(arr[(min_second_index as int)].len() >= 2) by {
            assert(0 <= (min_second_index as int) < (arr.len() as int));
        };

        let ghost old_min = min_second_index as int;
        let ghost old_index = index as int;

        if arr[index][1] < arr[min_second_index][1] {
            min_second_index = index;
        }

        let ghost new_min = min_second_index as int;
        assert(new_min == (if arr[old_index][1] < arr[old_min][1] { old_index } else { old_min })) by {
            if arr[old_index][1] < arr[old_min][1] {
                assert(min_second_index == index);
                assert(new_min == old_index);
            } else {
                assert(!(arr[old_index][1] < arr[old_min][1]));
                assert(min_second_index == (old_min as usize));
                assert(new_min == old_min);
            }
        };

        index += 1;

        proof {
            lemma_min_second_invariant_preserved(arr, old_min, old_index, new_min);
        }
    }
    // Fill in a block of assertions here to complete the proof;

    arr[min_second_index][0]
}

}