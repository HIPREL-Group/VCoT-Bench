use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_exists_witness_lt_index_impossible(text: &[u8], index: int)
    requires
        0 <= index <= text.len(),
        forall|k: int| 0 <= k < index ==> (text[k] != 90 && text[k] != 122),
    ensures
        !(exists|i: int| 0 <= i < index && (text[i] == 90 || text[i] == 122)),
{
    assert(forall|i: int| 0 <= i < index ==> !(text[i] == 90 || text[i] == 122)) by {
        let i = arbitrary::<int>();
        if 0 <= i < index {
            assert(text[i] != 90 && text[i] != 122);
            assert(!(text[i] == 90 || text[i] == 122)) by {
                assert(text[i] != 90);
                assert(text[i] != 122);
            }
        }
    };

    assert(!(exists|i: int| 0 <= i < index && (text[i] == 90 || text[i] == 122))) by {
        if exists|i: int| 0 <= i < index && (text[i] == 90 || text[i] == 122) {
            let i = choose|i: int| 0 <= i < index && (text[i] == 90 || text[i] == 122);
            assert(0 <= i < index);
            assert(text[i] == 90 || text[i] == 122);

            assert(!(text[i] == 90 || text[i] == 122)) by {
                assert(forall|j: int| 0 <= j < index ==> !(text[j] == 90 || text[j] == 122));
            }
            assert(false);
        }
    };
}

proof fn lemma_invariant_step(text: &[u8], index: int)
    requires
        0 <= index < text.len(),
        forall|k: int| 0 <= k < index ==> (text[k] != 90 && text[k] != 122),
        text[index] != 90 && text[index] != 122,
    ensures
        forall|k: int| 0 <= k < index + 1 ==> (text[k] != 90 && text[k] != 122),
{
    assert(forall|k: int| 0 <= k < index + 1 ==> (text[k] != 90 && text[k] != 122)) by {
        let k = arbitrary::<int>();
        if 0 <= k < index + 1 {
            if k < index {
                assert(text[k] != 90 && text[k] != 122);
            } else {
                assert(k == index);
                assert(text[k] != 90 && text[k] != 122) by {
                    assert(k == index);
                    assert(text[index] != 90 && text[index] != 122);
                }
            }
        }
    };
}

proof fn lemma_exists_at_index_implies_exists_in_len(text: &[u8], index: int)
    requires
        0 <= index < text.len(),
        text[index] == 90 || text[index] == 122,
    ensures
        exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122),
{
    let i: int = index;
    assert(exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)) by {
        assert(0 <= i);
        assert(i < text.len());
        assert(text[i] == 90 || text[i] == 122);
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall|k: int| 0 <= k < index ==> (text[k] != 90 && text[k] != 122),
    {
        if text[index] == 90 || text[index] == 122 {
            // Fill in a block of assertions here to complete the proof;
            return true;
        }
        // Fill in a block of assertions here to complete the proof

        index += 1;
    }

    assert(index == text.len());

    proof {
        lemma_exists_witness_lt_index_impossible(text, index as int);
    }

    assert(!(exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122))) by {
        assert(!(exists|i: int| 0 <= i < index as int && (text[i] == 90 || text[i] == 122)));
    };

    false
}

} // verus!