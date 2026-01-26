#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn fibo(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

proof fn fibo_is_monotonic(i: int, j: int)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i <= 0 {
        assert(fibo(i) == 0);
        assert(fibo(i) <= fibo(j));
    }
    else if i == j {
        assert(fibo(i) <= fibo(j));
    }
    else {
        fibo_is_monotonic(i, j - 1);

        assert(j - 1 >= 1) by {
            assert(i >= 1);
        };
        assert(j - 1 == 1 || j - 1 > 1);

        if j - 1 == 1 {
            assert(j == 2);
            assert(fibo(j) == fibo(0) + fibo(1));
            assert(fibo(0) == 0);
            assert(fibo(1) == 1);
            assert(fibo(j) >= fibo(j - 1));
        } else {
            assert(j - 1 > 1);
            assert(fibo(j) == fibo(j - 2) + fibo(j - 1));
            assert(fibo(j - 2) >= 0);
            assert(fibo(j) >= fibo(j - 1));
        }

        assert(fibo(i) <= fibo(j - 1));
        assert(fibo(j - 1) <= fibo(j));
        assert(fibo(i) <= fibo(j));
    }
}

proof fn lemma_fibo_fits_i32_monotone_prefix(i: usize, n: usize)
    requires
        i <= n,
        fibo_fits_i32(n as int),
    ensures
        fibo(i as int) < 0x8000_0000,
{
    fibo_is_monotonic(i as int, n as int);
    assert(fibo(i as int) <= fibo(n as int));
    assert(fibo(n as int) < 0x8000_0000);
    assert(fibo(i as int) < 0x8000_0000) by {
        assert(fibo(i as int) <= fibo(n as int));
        assert(fibo(n as int) < 0x8000_0000);
    };
}

#[verifier::exec_allows_no_decreases_clause]
fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i),
    ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);
    let mut i = 2;

    while i < n
        invariant
            forall |k: int| 0 <= k < i ==> #[trigger] fib@[k] == fibo(k),
            fibo_fits_i32(n as int),
            2 <= i,
            fib@.len() == i,
            i <= n,
    {
        proof{
            fibo_is_monotonic(i as int, n as int);
            assert(fibo(i as int) <= fibo(n as int));
            assert(fibo(n as int) < 0x8000_0000);

            lemma_fibo_fits_i32_monotone_prefix(i, n);
        }
        let next_fib = fib[i - 1] + fib[i - 2];

        fib.push(next_fib);

        i += 1;
    }

    fib
}
}