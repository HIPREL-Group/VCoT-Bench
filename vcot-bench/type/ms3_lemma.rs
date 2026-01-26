use vstd::prelude::*;
fn main() {}

verus! {

// Complete the lemma function below
proof fn lemma_i32_mod3_in_range(i: int)
    

// Complete the lemma function below
proof fn lemma_set_extends_prefix_range3(a: &Vec<i32>, i: usize)
   

#[verifier::exec_allows_no_decreases_clause]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            forall|k: int| 0 <= k < i ==> a[k] == 0 || a[k] == 1 || a[k] == 2,
            a.len() == N,
    {
        let tmp = (i % 3) as i32;

        assert(tmp == 0 || tmp == 1 || tmp == 2) by {
            let ii: int = i as int;
            lemma_i32_mod3_in_range(ii);
            assert((ii % 3) == 0 || (ii % 3) == 1 || (ii % 3) == 2);
            assert(tmp == 0 || tmp == 1 || tmp == 2);
        }

        a.set(i, tmp);

        assert(a[i as int] == 0 || a[i as int] == 1 || a[i as int] == 2) by {
            assert(tmp == 0 || tmp == 1 || tmp == 2);
        }

        i = i + 1;

        assert(forall|k: int| 0 <= k < i ==> a[k] == 0 || a[k] == 1 || a[k] == 2) by {
            lemma_set_extends_prefix_range3(a, (i - 1) as usize);
        }
    }

    i = 0;

    while (i < N as usize)
        invariant
            i <= N,
            forall|k: int| 0 <= k < N ==> a[k] == 0 || a[k] == 1 || a[k] == 2,
            a.len() == N,
            sum.len() == 1,
            i > 0 ==> sum[0] <= 2 * i,
            N < 1000,
    {
        if (i == 0) {
            sum.set(0, 0);

            assert(sum[0] <= 2 * (i + 1)) by {
                assert(sum[0] == 0);
                assert(0 <= 2 * (i + 1));
            }
        } else {
            let ai = a[i];
            assert(ai == 0 || ai == 1 || ai == 2) by {
                assert(a[i as int] == 0 || a[i as int] == 1 || a[i as int] == 2);
            }

            let sum_old = sum[0];
            assert(sum_old <= 2 * (i as i32)) by {
                assert(i > 0 ==> sum[0] <= 2 * i);
            }

            let temp = sum_old + a[i];
            sum.set(0, temp);

            assert(sum[0] <= 2 * ((i + 1) as i32)) by {
                assert(sum_old + ai <= 2 * ((i + 1) as i32));
                assert(sum[0] == sum_old + ai);
            }
        }
        i = i + 1;
    }

    assert(sum[0] <= 2 * N) by {
        assert(i > 0);
        assert(i > 0 ==> sum[0] <= 2 * i);
        assert(sum[0] <= 2 * i);
        assert(2 * i == 2 * (N as usize)) by {
            assert(i == N as usize);
        }
        assert((2 * (N as usize)) as int == (2 * N) as int);
        assert(sum[0] <= 2 * N);
    }
}

}