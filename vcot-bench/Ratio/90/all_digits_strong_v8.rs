use vstd::prelude::*;

fn main() {}
verus! {

spec fn is_ascii_digit_spec(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7'
        || c == '8' || c == '9'
}

fn is_ascii_digit(c: char) -> (r: bool)
    ensures
        r == is_ascii_digit_spec(c),
{
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7'
        || c == '8' || c == '9'
}

spec fn all_digits_spec(s: Seq<char>) -> bool {
    forall|i: nat| #![auto] i < s.len() ==> is_ascii_digit_spec(s[i as int])
}

proof fn lemma_all_digits_false_from_counterexample(s: Seq<char>, wit: nat)
    requires
        wit < s.len(),
        !is_ascii_digit_spec(s[wit as int]),
    ensures
        !all_digits_spec(s),
{
    assert(!all_digits_spec(s)) by {
        assert(!(forall|i: nat| i < s.len() ==> is_ascii_digit_spec(s[i as int]))) by {
            assert(!(wit < s.len() ==> is_ascii_digit_spec(s[wit as int])));
        }
    }
}

// Complete the lemma function below
proof fn lemma_all_digits_subrange_step(s: Seq<char>, i: nat)
   

// Complete the lemma function below
proof fn lemma_all_digits_spec_holds_for_empty_prefix(s: Seq<char>)
    

#[verifier::exec_allows_no_decreases_clause]
fn all_digits(s: String) -> (result: bool)
    requires
        s.is_ascii(),
    ensures
        all_digits_spec(s@) == result,
{
    let mut result = true;
    let mut i = 0;

    // Fill in a block of assertions here to complete the proof

    while i < s.as_str().unicode_len()
        // Fill in loop invariants here
    {
        let c = s.as_str().get_char(i);

        // Fill in a block of assertions here to complete the proof;

        if !is_ascii_digit(c) {
            // Fill in a block of assertions here to complete the proof
            return false;
        }

        // Fill in a block of assertions here to complete the proof

        i = i + 1;
    }

    // Fill in a block of assertions here to complete the proof
    true
}

} // verus!