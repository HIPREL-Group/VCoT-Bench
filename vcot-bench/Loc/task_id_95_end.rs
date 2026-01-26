use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_min_update_preserves_forall(
    list: &Vec<Vec<i32>>,
    index: usize,
    old_min: usize,
    new_min: usize,
)
    requires
        index < list.len(),
        new_min == list[(index as int)].len(),
        new_min < old_min,
        forall|k: int| 0 <= k < index ==> old_min <= #[trigger] list[k].len(),
    ensures
        forall|k: int| 0 <= k < index + 1 ==> new_min <= #[trigger] list[k].len(),
{
    assert(forall|k: int| 0 <= k < index + 1 ==> new_min <= #[trigger] list[k].len()) by {
        assert forall|k: int| 0 <= k < index + 1 implies new_min <= #[trigger] list[k].len() by {
            if 0 <= k < index + 1 {
                if k < index {
                    assert(old_min <= #[trigger] list[k].len());
                    assert(new_min <= old_min) by { assert(new_min < old_min); };
                    assert(new_min <= #[trigger] list[k].len()) by {
                        assert(new_min <= old_min);
                        assert(old_min <= #[trigger] list[k].len());
                    };
                } else {
                    assert(k == index) by {
                        assert(k >= index);
                        assert(k < index + 1);
                    };
                    assert(new_min <= #[trigger] list[k].len()) by {
                        assert(new_min == list[(index as int)].len());
                        assert(k == index);
                    };
                }
            }
        };
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
{
    let mut min = list[0].len();

    let mut index = 1;
    while index < list.len()
        invariant
            0 <= index <= list.len(),
            forall|k: int| 0 <= k < index ==> min <= #[trigger] list[k].len(),
            exists|k: int| 0 <= k < index && min == #[trigger] list[k].len(),
    {
        if (&list[index]).len() < min {
            let old_min = min;
            let new_min = (&list[index]).len();

            min = new_min;

            proof {
                lemma_min_update_preserves_forall(list, index, old_min, new_min);
            }
        } else {
            // Fill in a block of assertions here to complete the proof
        }
        index += 1;
    }
    min
}

}