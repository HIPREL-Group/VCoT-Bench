use vstd::prelude::*;
fn main() {
}

verus! {

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn shift32_spec(c: u8) -> u8 {
    (c + 32) as u8
}

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn shift_minus_32_spec(c: u8) -> u8 {
    (c - 32) as u8
}

spec fn to_toggle_case_spec(s: u8) -> u8 {
    if is_lower_case(s) {
        shift_minus_32_spec(s)
    } else if is_upper_case(s) {
        shift32_spec(s)
    } else {
        s
    }
}

// Complete the lemma function below
proof fn lemma_vec_push_extends_toggle_case(
    str1: &[u8],
    toggle_case: &Vec<u8>,
    index: usize,
)
   

#[verifier::exec_allows_no_decreases_clause]
fn to_toggle_case(str1: &[u8]) -> (toggle_case: Vec<u8>)
    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
{
    let mut toggle_case = Vec::with_capacity(str1.len());

    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            toggle_case.len() == index,
            forall|i: int|
                0 <= i < index ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
    {
        let c = str1[index];

        if (str1[index] >= 97 && str1[index] <= 122) {
            toggle_case.push((str1[index] - 32) as u8);

            assert(toggle_case[index as int] == to_toggle_case_spec(c));
        } else if (str1[index] >= 65 && str1[index] <= 90) {
            toggle_case.push((str1[index] + 32) as u8);

            assert(toggle_case[index as int] == to_toggle_case_spec(c));
        } else {
            toggle_case.push(str1[index]);

            assert(toggle_case[index as int] == to_toggle_case_spec(c));
        }

        assert(toggle_case.len() == index + 1);

        proof {
            assert(forall|i: int|
                0 <= i < (index + 1) ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i])) by {
                assert forall|i: int| 0 <= i < (index + 1) implies toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]) by {
                    if i == index as int {
                        assert(toggle_case[i] == to_toggle_case_spec(str1[(index as int)]));
                    } else {
                        assert(toggle_case[i] == to_toggle_case_spec(str1[i]));
                    }
                }
            }
        }

        index += 1;
    }
    toggle_case
}

} // verus!