use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_digit_sepc(c: u8) -> bool {
    c >= 48 && c <= 57
}

fn is_digit(c: u8) -> (res: bool)
    ensures
        res == is_digit_sepc(c),
{
    c >= 48 && c <= 57
}

// Complete the lemma function below
proof fn lemma_forall_extend_digit_prefix(text: &[u8], index: int)
   

// Complete the lemma function below
proof fn lemma_is_integer_loop_invariant_preserved(text: &[u8], index: int)
   

// Complete the lemma function below
proof fn lemma_is_integer_exit_implies_all_digits(text: &[u8], index: int)
   

#[verifier::exec_allows_no_decreases_clause]
fn is_integer(text: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
{
    let mut index = 0;
    while index < text.len()
        // Fill in loop invariants here
    {
        if (!is_digit(text[index])) {
            return false;
        }
        // Fill in a block of assertions here to complete the proof

        index += 1;
    }
    proof {
        lemma_is_integer_exit_implies_all_digits(text, (index as int));
    }
    true
}

} // verus!