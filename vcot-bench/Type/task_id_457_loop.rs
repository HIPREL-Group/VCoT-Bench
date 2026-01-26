use vstd::prelude::*;

fn main() {
}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= #[trigger] (seq[k]@),
{
    let mut min_list = &seq[0];
    assert(min_list@ =~= seq[0]@);
    let mut index = 1;

    while index < seq.len()
        // Fill in loop invariants here
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
            assert(min_list@ =~= seq[(index as int)]@);
        }
        index += 1;
    }
    min_list
}

} // verus!