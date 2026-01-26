use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_interleave_push_preserves_prefix(
    s1: &Vec<i32>,
    s2: &Vec<i32>,
    s3: &Vec<i32>,
    output_seq: &Vec<i32>,
    index: usize,
)
    requires
        s1@.len() == s2@.len(),
        s2@.len() == s3@.len(),
        0 <= index <= s1@.len(),
        output_seq@.len() == 3 * index,
        forall|k: int|
            0 <= k < index ==> (
                output_seq[3 * k] == s1[k]
                    && output_seq[3 * k + 1] == s2[k]
                    && output_seq[3 * k + 2] == s3[k]
            ),
        index < s1@.len(),
    ensures
        ({
            let out1 = output_seq@.push(s1[index as int]);
            let out2 = out1.push(s2[index as int]);
            let out3 = out2.push(s3[index as int]);
            out3.len() == 3 * (index + 1)
                && forall|k: int|
                    0 <= k < index + 1 ==> (
                        out3[3 * k] == s1[k]
                            && out3[3 * k + 1] == s2[k]
                            && out3[3 * k + 2] == s3[k]
                    )
        }),
{
    let out1 = output_seq@.push(s1[index as int]);
    let out2 = out1.push(s2[index as int]);
    let out3 = out2.push(s3[index as int]);

    assert(out3.len() == 3 * (index + 1));

    assert(forall|k: int|
        0 <= k < index ==> (
            out3[3 * k] == s1[k]
                && out3[3 * k + 1] == s2[k]
                && out3[3 * k + 2] == s3[k]
        )) by {
        assert(forall|k: int|
            0 <= k < index ==> (
                out1[3 * k] == s1[k]
                    && out1[3 * k + 1] == s2[k]
                    && out1[3 * k + 2] == s3[k]
            )) by {
            assert(forall|k: int|
                0 <= k < index ==> (
                    #[trigger] out1[3 * k] == output_seq@[3 * k]
                        && #[trigger] out1[3 * k + 1] == output_seq@[3 * k + 1]
                        && #[trigger] out1[3 * k + 2] == output_seq@[3 * k + 2]
                ));
        };
        assert(forall|k: int|
            0 <= k < index ==> (
                out2[3 * k] == s1[k]
                    && out2[3 * k + 1] == s2[k]
                    && out2[3 * k + 2] == s3[k]
            )) by {
            assert(forall|k: int|
                0 <= k < index ==> (
                    #[trigger] out2[3 * k] == out1[3 * k]
                        && #[trigger] out2[3 * k + 1] == out1[3 * k + 1]
                        && #[trigger] out2[3 * k + 2] == out1[3 * k + 2]
                ));
        };
        assert(forall|k: int|
            0 <= k < index ==> (
                out3[3 * k] == s1[k]
                    && out3[3 * k + 1] == s2[k]
                    && out3[3 * k + 2] == s3[k]
            )) by {
            assert(forall|k: int|
                0 <= k < index ==> (
                    #[trigger] out3[3 * k] == out2[3 * k]
                        && #[trigger] out3[3 * k + 1] == out2[3 * k + 1]
                        && #[trigger] out3[3 * k + 2] == out2[3 * k + 2]
                ));
        };
    };

    assert(
        out3[3 * (index as int)] == s1[index as int]
        && out3[3 * (index as int) + 1] == s2[index as int]
        && out3[3 * (index as int) + 2] == s3[index as int]
    ) by {
        assert(out1[output_seq@.len() as int] == s1[index as int]);
        assert(out2[out1.len() as int] == s2[index as int]);
        assert(out3[out2.len() as int] == s3[index as int]);

        assert(out1[3 * (index as int)] == s1[index as int]) by {
            assert(3 * (index as int) == output_seq@.len());
        };
        assert(out2[3 * (index as int)] == s1[index as int]) by {
            assert(3 * (index as int) < out1.len());
        };
        assert(out3[3 * (index as int)] == s1[index as int]) by {
            assert(3 * (index as int) < out2.len());
        };

        assert(out2[3 * (index as int) + 1] == s2[index as int]) by {
            assert(3 * (index as int) + 1 == out1.len() as int);
        };
        assert(out3[3 * (index as int) + 1] == s2[index as int]) by {
            assert(3 * (index as int) + 1 < out2.len());
        };

        assert(out3[3 * (index as int) + 2] == s3[index as int]) by {
            assert(3 * (index as int) + 2 == out2.len() as int);
        };
    };

    assert(forall|k: int|
        0 <= k < index + 1 ==> (
            out3[3 * k] == s1[k]
                && out3[3 * k + 1] == s2[k]
                && out3[3 * k + 2] == s3[k]
        )) by {
        assert(forall|k: int|
            0 <= k < index ==> (
                out3[3 * k] == s1[k]
                    && out3[3 * k + 1] == s2[k]
                    && out3[3 * k + 2] == s3[k]
            ));
        assert(
            out3[3 * (index as int)] == s1[index as int]
            && out3[3 * (index as int) + 1] == s2[index as int]
            && out3[3 * (index as int) + 2] == s3[index as int]
        );
    };
}

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
        invariant
            0 <= index <= s1.len(),
            output_seq@.len() == 3 * index,
            s1@.len() == s2@.len() && s2@.len() == s3@.len(),
            forall|k: int|
                0 <= k < index ==> (output_seq[3 * k] == s1[k] && output_seq[3 * k + 1] == s2[k]
                    && output_seq[3 * k + 2] == s3[k]),
    {
        let ghost old_seq = output_seq@;
        // Fill in a block of assertions here to complete the proof

        output_seq.push(s1[index]);
        output_seq.push(s2[index]);
        output_seq.push(s3[index]);

        assert(output_seq@.len() == 3 * (index + 1)) by {
            assert(output_seq@.len() == 3 * index + 3);
        };

        assert(forall|k: int|
            0 <= k < index + 1 ==> (
                output_seq@[3 * k] == s1[k]
                    && output_seq@[3 * k + 1] == s2[k]
                    && output_seq@[3 * k + 2] == s3[k]
            )) by {
            let out1 = old_seq.push(s1[index as int]);
            let out2 = out1.push(s2[index as int]);
            let out3 = out2.push(s3[index as int]);
            assert(output_seq@ == out3);
        };

        index += 1;
    }
    output_seq
}

} // verus!