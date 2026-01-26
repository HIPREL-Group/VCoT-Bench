use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn conditional_average(
    vals_1: &Vec<u64>,
    vals_2: &Vec<u64>,
    conds_1: &Vec<bool>,
    conds_2: &Vec<bool>,
    avgs: &mut Vec<u64>,
)
    requires
        vals_1.len() == vals_2.len(),
        vals_1.len() == conds_1.len(),
        vals_1.len() == conds_2.len(),
        forall|idx: int| 0 <= idx < vals_1.len() ==> conds_1[idx] || conds_2[idx],
        forall|idx: int| 0 <= idx < vals_1.len() ==> vals_1[idx] < 1000,
        forall|idx: int| 0 <= idx < vals_2.len() ==> vals_2[idx] < 1000,
    ensures
        avgs.len() == vals_1.len(),
        forall|idx: int|
            0 <= idx < vals_1.len() ==> (
                (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2)
                    && (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx])
                    && (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
            ),
{
    let mut k: usize = 0;
    let common_len = vals_1.len();
    avgs.clear();

    while (k < common_len)
        invariant
            k <= common_len,
            avgs.len() == k,
            vals_1.len() == common_len,
            vals_2.len() == common_len,
            conds_1.len() == common_len,
            conds_2.len() == common_len,
            forall|idx: int| 0 <= idx < vals_1.len() ==> vals_1[idx] < 1000,
            forall|idx: int| 0 <= idx < vals_2.len() ==> vals_2[idx] < 1000,
            forall|i: int|
                0 <= i < k ==> (
                    (conds_1[i] && conds_2[i] ==> avgs[i] == (vals_1[i] + vals_2[i]) / 2)
                        && (conds_1[i] && !conds_2[i] ==> avgs[i] == vals_1[i])
                        && (!conds_1[i] && conds_2[i] ==> avgs[i] == vals_2[i])
                ),
    {
        let mut new_avg: u64 = 0;

        if (conds_1[k]) {
            if (conds_2[k]) {
                new_avg = (vals_1[k] + vals_2[k]) / 2;
            } else {
                new_avg = vals_1[k];
            }
        } else {
            new_avg = vals_2[k];
        }

        let old_k: usize = k;
        avgs.push(new_avg);
        k = k + 1;

        proof {
            assert(avgs.len() == k);

            assert(forall|i: int|
                0 <= i < k ==> (
                    (conds_1[i] && conds_2[i] ==> avgs[i] == (vals_1[i] + vals_2[i]) / 2)
                        && (conds_1[i] && !conds_2[i] ==> avgs[i] == vals_1[i])
                        && (!conds_1[i] && conds_2[i] ==> avgs[i] == vals_2[i])
                )) by {
                let i: int = arbitrary();
                if 0 <= i < k {
                    if i < old_k {
                        assert(
                            (conds_1[i] && conds_2[i] ==> avgs[i] == (vals_1[i] + vals_2[i]) / 2)
                                && (conds_1[i] && !conds_2[i] ==> avgs[i] == vals_1[i])
                                && (!conds_1[i] && conds_2[i] ==> avgs[i] == vals_2[i])
                        );
                    } else {
                        if conds_1[(old_k as int)] {
                            if conds_2[(old_k as int)] {
                                assert(avgs[(old_k as int)] == new_avg);
                                assert(conds_1[(old_k as int)] && conds_2[(old_k as int)]
                                    ==> avgs[(old_k as int)] == (vals_1[(old_k as int)] + vals_2[(old_k as int)]) / 2);
                                assert(conds_1[(old_k as int)] && !conds_2[(old_k as int)]
                                    ==> avgs[(old_k as int)] == vals_1[(old_k as int)]);
                                assert(!conds_1[(old_k as int)] && conds_2[(old_k as int)]
                                    ==> avgs[(old_k as int)] == vals_2[(old_k as int)]);
                            } else {
                                assert(avgs[(old_k as int)] == new_avg);
                                assert(conds_1[(old_k as int)] && conds_2[(old_k as int)]
                                    ==> avgs[(old_k as int)] == (vals_1[(old_k as int)] + vals_2[(old_k as int)]) / 2);
                                assert(conds_1[(old_k as int)] && !conds_2[(old_k as int)]
                                    ==> avgs[(old_k as int)] == vals_1[(old_k as int)]);
                                assert(!conds_1[(old_k as int)] && conds_2[(old_k as int)]
                                    ==> avgs[(old_k as int)] == vals_2[(old_k as int)]);
                            }
                        } else {
                            assert(avgs[(old_k as int)] == new_avg);
                            assert(conds_1[(old_k as int)] && conds_2[(old_k as int)]
                                ==> avgs[(old_k as int)] == (vals_1[(old_k as int)] + vals_2[(old_k as int)]) / 2);
                            assert(conds_1[(old_k as int)] && !conds_2[(old_k as int)]
                                ==> avgs[(old_k as int)] == vals_1[(old_k as int)]);
                            assert(!conds_1[(old_k as int)] && conds_2[(old_k as int)]
                                ==> avgs[(old_k as int)] == vals_2[(old_k as int)]);
                        }
                    }
                }
            };
        }
    }
}

}