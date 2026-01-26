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

proof fn lemma_forall_k_lt_index_preserved<T>(seq: &Vec<Vec<T>>, index: usize)
    requires
        index < seq.len(),
        forall|k: int| 0 <= k < (index as int) ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
        (&seq[(index as int)]).len() == (&seq[0]).len(),
    ensures
        forall|k: int| 0 <= k < (index as int) + 1 ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
{
    assert(forall|k: int| 0 <= k < (index as int) + 1 ==> (#[trigger] seq[k].len() == (&seq[0]).len())) by {
        let k: int = arbitrary();
        if 0 <= k < (index as int) + 1 {
            if k < (index as int) {
                assert(seq[k].len() == (&seq[0]).len());
            } else {
                assert(k == (index as int));
                assert(seq[k].len() == (&seq[0]).len());
            }
        }
    }
}

proof fn lemma_all_k_lt_len_from_loop_invariant<T>(seq: &Vec<Vec<T>>, index: usize)
    requires
        index == seq.len(),
        forall|k: int| 0 <= k < (index as int) ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
    ensures
        forall|k: int| 0 <= k < seq.len() ==> (#[trigger] seq[k].len() == (&seq[0]).len()),
{
    assert(forall|k: int| 0 <= k < seq.len() ==> (#[trigger] seq[k].len() == (&seq[0]).len())) by {
        let k: int = arbitrary();
        if 0 <= k < seq.len() {
            assert(0 <= k < (index as int));
            assert(seq[k].len() == (&seq[0]).len());
        }
    }
}

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

        proof {
            lemma_forall_k_lt_index_preserved(seq, index);
        }

        index += 1;
    }

    assert(index == seq.len());

    proof {
        lemma_all_k_lt_len_from_loop_invariant(seq, index);
    }

    proof {
        lemma_all_equal_to_first_implies_pairwise_len(seq);
    }

    true
}

}