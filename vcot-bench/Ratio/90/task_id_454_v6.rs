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
        // Fill in loop invariants here
    {
        if text[index] == 90 || text[index] == 122 {
            // Fill in a block of assertions here to complete the proof;
            return true;
        }
        assert(text[(index as int)] != 90 && text[(index as int)] != 122);

        proof {
            lemma_invariant_step(text, index as int);
        }

        index += 1;
    }

    // Fill in a block of assertions here to complete the proof;

    false
}

} // verus!