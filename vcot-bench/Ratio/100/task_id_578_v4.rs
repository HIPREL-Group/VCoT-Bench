use vstd::prelude::*;

fn main() {
}

verus! {

// Complete the lemma function below
proof fn lemma_interleave_push_preserves_prefix(
    s1: &Vec<i32>,
    s2: &Vec<i32>,
    s3: &Vec<i32>,
    output_seq: &Vec<i32>,
    index: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn interleave(s1: &Vec<i32>, s2: &Vec<i32>, s3: &Vec<i32>) -> (res: Vec<i32>)
    requires
        s1@.len() == s2@.len() && s2@.len() == s3@.len(),
        0 <= (s1@.len() * 3) <= i32::MAX,
    ensures
        res@.len() == s1@.len() * 3,
        forall|i: int|
            0 <= i < s1@.len() ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2]
                == s3[i]),
{
    let new_seq_len = s1.len() * 3;
    let mut output_seq = Vec::with_capacity(new_seq_len);
    let mut index = 0;

    while index < s1.len()
        // Fill in loop invariants here
    {
        let ghost old_seq = output_seq@;
        // Fill in a block of assertions here to complete the proof

        output_seq.push(s1[index]);
        output_seq.push(s2[index]);
        output_seq.push(s3[index]);

        // Fill in a block of assertions here to complete the proof;

        index += 1;
    }
    output_seq
}

} // verus!