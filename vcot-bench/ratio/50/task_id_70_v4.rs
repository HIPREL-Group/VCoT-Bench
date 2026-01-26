use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_all_equal_to_first_implies_pairwise<T>(s: Seq<T>)
    ensures
        (forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] == s[0])
        ==> (forall|i: int, j: int|
                (0 <= i < s.len() && 0 <= j < s.len()) ==> (#[trigger] s[i] == #[trigger] s[j])),
{
    if !(forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] == s[0]) {
        return;
    }
    assert(forall|i: int, j: int|
        (0 <= i < s.len() && 0 <= j < s.len()) ==> s[i] == s[j]) by {
        let i: int = arbitrary();
        let j: int = arbitrary();
        if 0 <= i < s.len() && 0 <= j < s.len() {
            assert(s[i] == s[0]);
            assert(s[j] == s[0]);
            assert(s[i] == s[j]);
        }
    }
}

// Complete the lemma function below
proof fn lemma_forall_k_lt_index_preserved<T>(seq: &Vec<Vec<T>>, index: usize)
   

// Complete the lemma function below
proof fn lemma_all_k_lt_len_from_loop_invariant<T>(seq: &Vec<Vec<T>>, index: usize)
   

proof fn lemma_all_equal_to_first_implies_pairwise_len<T>(seq: &Vec<Vec<T>>)
    requires
        forall|k: int| 0 <= k < seq.len() ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
    ensures
        forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len() == #[trigger] seq[j].len()),
{
    assert(forall|i: int, j: int|
        (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len() == #[trigger] seq[j].len())) by {
        let i: int = arbitrary();
        let j: int = arbitrary();
        if 0 <= i < seq.len() && 0 <= j < seq.len() {
            assert(seq[i].len() == (&seq[0]).len());
            assert(seq[j].len() == (&seq[0]).len());
            assert(seq[i].len() == seq[j].len());
        }   
    }
}

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
        invariant
            1 <= index <= seq.len(),
            forall|k: int| 0 <= k < index ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
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