use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_all_equal_to_first_implies_pairwise<T>(s: Seq<T>)
    

// Complete the lemma function below
proof fn lemma_forall_k_lt_index_preserved<T>(seq: &Vec<Vec<T>>, index: usize)
   

// Complete the lemma function below
proof fn lemma_all_k_lt_len_from_loop_invariant<T>(seq: &Vec<Vec<T>>, index: usize)
   

// Complete the lemma function below
proof fn lemma_all_equal_to_first_implies_pairwise_len<T>(seq: &Vec<Vec<T>>)
   

#[verifier::exec_allows_no_decreases_clause]
fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)
    requires
        seq.len() > 0,
    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
{
    let mut index = 1;

    while index < seq.len()
        // Fill in loop invariants here
    {
        if ((&seq[index]).len() != (&seq[0]).len()) {
            assert(!((forall|k: int| 0 <= k < seq.len() ==> (#[trigger] seq[k].len() == (&seq[0]).len())))) by {
                let k: int = (index as int);
                assert(0 <= k);
                assert(k < seq.len());
                assert(seq[k].len() != (&seq[0]).len());
            }

            assert(!((forall|i: int, j: int|
                (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len() == #[trigger] seq[j].len())))) by {
                let i: int = (index as int);
                let j: int = 0;
                assert(0 <= i < seq.len());
                assert(0 <= j < seq.len());
                assert(seq[i].len() != seq[j].len());
            }
            return false;
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof

    true
}

}