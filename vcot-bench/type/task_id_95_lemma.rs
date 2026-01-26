use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_min_update_preserves_forall(
    list: &Vec<Vec<i32>>,
    index: usize,
    old_min: usize,
    new_min: usize,
)
   

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
            proof {
                assert(forall|k: int| 0 <= k < index + 1 ==> min <= #[trigger] list[k].len()) by {
                    assert forall|k: int| 0 <= k < index + 1 implies min <= #[trigger] list[k].len() by {
                        if 0 <= k < index + 1 {
                            if k < index {
                                assert(min <= #[trigger] list[k].len());
                            } else {
                                assert(k == index) by {
                                    assert(k >= index);
                                    assert(k < index + 1);
                                };
                                assert(min <= #[trigger] list[k].len()) by {
                                    assert(k == index);
                                    assert(min <= list[(index as int)].len());
                                };
                            }
                        }
                    };
                };
                assert(exists|k: int| 0 <= k < index + 1 && min == #[trigger] list[k].len()) by {
                    let ex = choose|k: int| 0 <= k < index && min == #[trigger] list[k].len();
                    assert(0 <= ex && ex < index);
                    assert(ex < index + 1);
                };
            }
        }
        index += 1;
    }
    min
}

}