use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_exists_preserved_if_max_unchanged(
    seq: &Vec<Vec<i32>>,
    old_max: &Vec<i32>,
    new_max: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_using_compare(
    seq: &Vec<Vec<i32>>,
    old_max: &Vec<i32>,
    new_max: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_exists_extend_by_one_with_new_index(
    seq: &Vec<Vec<i32>>,
    new_max: &Vec<i32>,
    index: int,
)
   

// Complete the lemma function below
proof fn lemma_forall_extend_by_one_when_update(
    seq: &Vec<Vec<i32>>,
    old_max: &Vec<i32>,
    new_max: &Vec<i32>,
    index: int,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
{
    let mut max_list = &seq[0];
    assert(max_list@ =~= seq[0]@);
    let mut index = 1;

    while index < seq.len()
        invariant
            0 <= index <= seq.len(),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|k: int| 0 <= k < index && max_list@ =~= #[trigger] (seq[k]@),
    {
        if ((seq[index]).len() > max_list.len()) {
            let old_max = max_list;
            max_list = &seq[index];

            assert(max_list@ =~= seq[(index as int)]@);

            proof {
                lemma_forall_extend_by_one_when_update(seq, old_max, max_list, index as int);
                lemma_exists_extend_by_one_with_new_index(seq, max_list, index as int);
            }
        } else {
            let old_max = max_list;
            assert(old_max@ =~= max_list@);

            proof {
                lemma_forall_extend_by_one_using_compare(seq, old_max, max_list, index as int);
                lemma_exists_preserved_if_max_unchanged(seq, old_max, max_list, index as int);
            }
        }

        index += 1;
    }

    assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len());
    assert(exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@));

    max_list
}

} // verus!