use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_exists_witness_lt_index_impossible(text: &[u8], index: int)
   

// Complete the lemma function below
proof fn lemma_invariant_step(text: &[u8], index: int)
   

// Complete the lemma function below
proof fn lemma_exists_at_index_implies_exists_in_len(text: &[u8], index: int)
   

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
            proof {
                lemma_exists_at_index_implies_exists_in_len(text, index as int);
            }
            assert(exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)) by {
                let i: int = index as int;
                assert(0 <= i);
                assert(i < text.len());
                assert(text[i] == 90 || text[i] == 122);
            };
            return true;
        }
        assert(text[(index as int)] != 90 && text[(index as int)] != 122);

        proof {
            lemma_invariant_step(text, index as int);
        }

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