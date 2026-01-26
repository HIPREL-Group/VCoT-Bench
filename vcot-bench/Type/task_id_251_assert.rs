use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_insert_before_each_step(
    arr: &Vec<i32>,
    elem: i32,
    result_old: Seq<i32>,
    index: int,
    result_new: Seq<i32>,
)
    requires
        0 <= index < arr.len(),
        result_old.len() == index * 2,
        forall|k: int| 0 <= k < index ==> #[trigger] result_old[2 * k] == elem,
        forall|k: int| 0 <= k < index ==> #[trigger] result_old[2 * k + 1] == arr[k],
        result_new == result_old.push(elem).push(arr[index]),
    ensures
        result_new.len() == (index + 1) * 2,
        forall|k: int| 0 <= k < index + 1 ==> #[trigger] result_new[2 * k] == elem,
        forall|k: int| 0 <= k < index + 1 ==> #[trigger] result_new[2 * k + 1] == arr[k],
{
    assert forall|k: int| 0 <= k < index + 1 implies #[trigger] result_new[2 * k] == elem by {
        if k < index {
            assert(result_new[2 * k] == result_old.push(elem).push(arr[index])[2 * k]);
            assert(result_old.push(elem)[2 * k] == result_old[2 * k]);
            assert(result_new[2 * k] == result_old[2 * k]);
            assert(result_old[2 * k] == elem);
        } else {
            assert(result_old.push(elem)[(result_old.len() as int)] == elem);
            assert(result_new[2 * k] == result_old.push(elem).push(arr[index])[(result_old.len() as int)]);
            assert(result_new[2 * k] == elem);
        }
    };

    assert forall|k: int| 0 <= k < index + 1 implies #[trigger] result_new[2 * k + 1] == arr[k] by {
        if k < index {
            assert(result_old.push(elem)[2 * k + 1] == result_old[2 * k + 1]);
            assert(result_new[2 * k + 1] == result_old.push(elem).push(arr[index])[2 * k + 1]);
            assert(result_new[2 * k + 1] == result_old[2 * k + 1]);
            assert(result_old[2 * k + 1] == arr[k]);
        } else {
            assert(result_new[2 * k + 1] == result_old.push(elem).push(arr[index])[(result_old.len() as int) + 1]);
            assert(result_old.push(elem).push(arr[index])[(result_old.push(elem).len() as int)] == arr[index]);
            assert(result_new[2 * k + 1] == arr[index]);
            assert(result_new[2 * k + 1] == arr[k]);
        }
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            result@.len() == index * 2,
            forall|k: int| 0 <= k < index ==> #[trigger] result[2 * k] == elem,
            forall|k: int| 0 <= k < index ==> #[trigger] result[2 * k + 1] == arr[k],
    {
        let ghost old_seq = result@;

        result.push(elem);
        result.push(arr[index]);

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    result
}

} // verus!