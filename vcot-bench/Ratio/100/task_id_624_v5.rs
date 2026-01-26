use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn shift_minus_32_spec(c: u8) -> u8 {
    (c - 32) as u8
}

// Complete the lemma function below
proof fn lemma_forall_extend_one(
    str1: &[u8],
    upper_case: Seq<u8>,
    index: int,
    new_val: u8,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn to_uppercase(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })),
{
    let mut upper_case: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        // Fill in loop invariants here
    {
        let c = str1[index];

        if (str1[index] >= 97 && str1[index] <= 122) {
            upper_case.push((str1[index] - 32) as u8);
        } else {
            upper_case.push(str1[index]);
        }

        // Fill in a block of assertions here to complete the proof

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    // Fill in a block of assertions here to complete the proof;
    upper_case
}

} // verus!