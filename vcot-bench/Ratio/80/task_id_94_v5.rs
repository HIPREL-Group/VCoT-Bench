use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_min_second_invariant_preserved(
    arr: &Vec<Vec<i32>>,
    min_second_index: int,
    index: int,
    new_min_second_index: int,
)
   

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
        // Fill in loop invariants here
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
        // Fill in a block of assertions here to complete the proof;

        index += 1;

        // Fill in a block of assertions here to complete the proof
    }
    // Fill in a block of assertions here to complete the proof;

    arr[min_second_index][0]
}

}