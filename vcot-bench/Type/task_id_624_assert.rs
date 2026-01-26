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

proof fn lemma_forall_extend_one(
    str1: &[u8],
    upper_case: Seq<u8>,
    index: int,
    new_val: u8,
)
    requires
        0 <= index,
        index < str1@.len(),
        upper_case.len() == index,
        forall|i: int|
            0 <= i < index ==> (upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })),
        new_val == (if is_lower_case(str1[index]) {
            shift_minus_32_spec(str1[index])
        } else {
            str1[index]
        }),
    ensures
        forall|i: int|
            0 <= i < index + 1 ==> (upper_case.push(new_val)[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })),
{
    assert(forall|i: int|
        0 <= i < index + 1 ==> (upper_case.push(new_val)[i] == (if is_lower_case(#[trigger] str1[i]) {
            shift_minus_32_spec(str1[i])
        } else {
            str1[i]
        }))) by {
        assert forall|i: int|
            0 <= i < index + 1 implies (upper_case.push(new_val)[i] == (if is_lower_case(#[trigger] str1[i]) {
                shift_minus_32_spec(str1[i])
            } else {
                str1[i]
            })) by
        {
            if i < index {
                assert(upper_case.push(new_val)[i] == upper_case[i]);
                assert(upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
                    shift_minus_32_spec(str1[i])
                } else {
                    str1[i]
                }));
            } else {
                assert(i == index);
                assert(upper_case.push(new_val)[i] == new_val);
                assert(new_val == (if is_lower_case(str1[index]) {
                    shift_minus_32_spec(str1[index])
                } else {
                    str1[index]
                }));
            }
        }
    };
}

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
        invariant
            0 <= index <= str1.len(),
            upper_case.len() == index,
            forall|i: int|
                0 <= i < index ==> (upper_case[i] == (if is_lower_case(#[trigger] str1[i]) {
                    shift_minus_32_spec(str1[i])
                } else {
                    str1[i]
                })),
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