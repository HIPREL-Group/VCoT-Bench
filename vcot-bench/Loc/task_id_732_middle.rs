use vstd::prelude::*;

fn main() {
}

verus! {

spec fn is_space_comma_dot_spec(c: u8) -> bool {
    (c == 32) || (c == 44) || (c == 46)
}

proof fn lemma_extend_pointwise_property_for_push(
    str1: Seq<u8>,
    old_res: Seq<u8>,
    index: int,
    pushed: u8,
)
    requires
        0 <= index,
        old_res.len() == index,
        forall|k: int|
            0 <= k < index ==> #[trigger] old_res[k]
                == (if is_space_comma_dot_spec(str1[k]) { 58 } else { str1[k] }),
        pushed == (if is_space_comma_dot_spec(str1[index]) { 58 } else { str1[index] }),
    ensures
        forall|k: int|
            0 <= k < index + 1 ==> #[trigger] old_res.push(pushed)[k]
                == (if is_space_comma_dot_spec(str1[k]) { 58 } else { str1[k] }),
{
    assert(forall|k: int|
        0 <= k < index ==> #[trigger] old_res.push(pushed)[k]
            == (if is_space_comma_dot_spec(str1[k]) { 58 } else { str1[k] })) by {
        assert(forall|k: int|
            0 <= k < index ==> #[trigger] old_res.push(pushed)[k] == old_res[k]);
    };

    assert(old_res.push(pushed)[index] == pushed);
}

#[verifier::exec_allows_no_decreases_clause]
fn replace_with_colon(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                58 
            } else {
                str1[k]
            }),
{
    let mut result: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;

    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            result@.len() == index,
            forall|k: int|
                0 <= k < index ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) {
                    58  
                } else {
                    str1[k]
                }),
    {
        let c = str1[index];

        let ghost old_res = result@;

        if ((str1[index] == 32) || (str1[index] == 44) || (str1[index] == 46)) {
            result.push(58); 
        } else {
            result.push(str1[index]);
        }

        // Fill in a block of assertions here to complete the proof;

        index += 1;

        // Fill in a block of assertions here to complete the proof;
    }

    assert(forall|k: int|
        0 <= k < result.len() ==> #[trigger] result[k] == (if is_space_comma_dot_spec(str1[k]) { 58 } else { str1[k] })) by {
        assert(index == result.len());
    };

    result
}

} // verus!