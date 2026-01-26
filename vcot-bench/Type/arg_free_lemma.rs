use vstd::prelude::*;
fn main() {}

verus!{

// Complete the lemma function below
proof fn lemma_gap_preserved_by_inc(gap: u64, res: u64, idx: u64)
   

#[verifier::exec_allows_no_decreases_clause]
fn choose_odd()
{
    let mut idx: u64 = 0;
    let mut res: u64 = 5;

    let ghost gap = res-idx;

    assert(gap < 100) by {
        assert(res == 5);
        assert(idx == 0);
        assert(gap == 5);
        assert(5 < 100);
    }

    while (idx < 10)
    invariant
        idx<=10,
        0 <= gap,
        gap<100,
        gap==res-idx,
    {
        assert(idx < 10);

        assert(idx + 1 <= res + 1) by {
            assert(res == gap + idx);
        }

        let ghost idx_old = idx;
        let ghost res_old = res;

        res = res + 1;
        idx = idx + 1;

        assert(idx <= 10) by {
            assert(idx_old < 10);
            assert(idx_old + 1 <= 10);
        }

        assert(gap == res - idx) by {
            lemma_gap_preserved_by_inc((gap as u64), res_old, idx_old);
            assert(gap == (res_old + 1) - (idx_old + 1));
            assert(res == res_old + 1);
            assert(idx == idx_old + 1);
        }
    }
    idx = 0;

    let ghost gap = res - idx;

    assert(gap < 100) by {
        assert(res == 15);
        assert(idx == 0);
        assert(gap == 15);
        assert(15 < 100);
    }

    while (idx < 10)
    invariant
        idx<=10,
        0 <= gap,
        gap<100,
        gap==res-idx,
    {

        assert(idx < 10);

        assert(idx + 1 <= res + 1) by {
            assert(res == gap + idx);
        }

        let ghost idx_old = idx;
        let ghost res_old = res;

        res = res + 1;
        idx = idx + 1;

        assert(idx <= 10) by {
            assert(idx_old < 10);
            assert(idx_old + 1 <= 10);
        }

        assert(gap == res - idx) by {
            lemma_gap_preserved_by_inc((gap as u64), res_old, idx_old);
            assert(gap == (res_old + 1) - (idx_old + 1));
            assert(res == res_old + 1);
            assert(idx == idx_old + 1);
        }
    }

    assert(res == 25);
}
}