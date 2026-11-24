"""Independent numerical cross-check of the Lean definitions and theorem statements.

Plain Python, no dependencies. Run:  python3 lean/scripts/check_definitions.py
It recomputes, by brute force, the quantities the Lean files talk about and checks every
formal statement in WSS/*.lean on small cases. This guards against a definition in Lean
meaning something different from what the docstrings say (the proofs themselves are
checked by Lean).
"""


def pisano(m):
    """Least k > 0 with F(k) = 0 and F(k+1) = 1 mod m (brute force)."""
    if m == 1:
        return 1
    a, b, k = 0, 1, 0
    while True:
        a, b, k = b, (a + b) % m, k + 1
        if a == 0 and b == 1:
            return k


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def primes(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return [i for i in range(n + 1) if s[i]]


def legendre(a, p):
    r = pow(a % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r


def wall_index(p):  # Lean: if legendreSym 5 p = 1 then p - 1 else p + 1
    return p - 1 if legendre(p, 5) == 1 else p + 1


def main():
    # Known small values (OEIS A001175).
    known = {1: 1, 2: 3, 3: 8, 4: 6, 5: 20, 6: 24, 7: 16, 8: 12, 9: 24, 10: 60, 11: 10}
    for m, v in known.items():
        assert pisano(m) == v, (m, pisano(m), v)

    # isFibPeriod_iff_pisano_dvd, even_pisano, isFibPeriod_four_mul (m up to 300).
    for m in range(1, 301):
        P = pisano(m)
        for k in range(0, 3 * P + 1):
            per = fib(k) % m == 0 and fib(k + 1) % m == 1 % m
            assert per == (k % P == 0), (m, k)
        if m > 2:
            assert P % 2 == 0, m
        for a in range(1, 60):
            if fib(a) % m == 0:
                assert (4 * a) % P == 0, (m, a)

    count = 0
    for p in primes(3000):
        if p in (2, 5):
            continue
        N = wall_index(p)
        e5p = legendre(5, p)  # (5/p)
        assert e5p == legendre(p, 5)  # quadratic reciprocity instance
        assert (e5p == 1) == (p % 5 in (1, 4))  # legendreSym_five_eq_one_iff
        assert N == p - legendre(p, 5)  # wallIndex_eq
        FN = fib(N)
        assert FN % p == 0  # prime_dvd_fib_wallIndex
        assert fib(p) % p == e5p % p  # fib_prime_zmod
        assert (2 * fib(p - 1) - (1 - e5p)) % p == 0  # two_mul_fib_prime_sub_one_zmod
        Pp, Pp2 = pisano(p), pisano(p * p)
        if e5p == 1:
            assert (p - 1) % Pp == 0
        else:
            assert (2 * (p + 1)) % Pp == 0  # pisano_prime_dvd
        assert Pp2 in (Pp, p * Pp)  # pisano_sq_eq_or
        assert Pp % p != 0  # not_dvd_pisano
        wss = FN % (p * p) == 0
        assert wss == (Pp2 == Pp)  # wall_equivalence
        assert wss == ((FN // p) % p == 0)  # isWallSunSunPrime_iff_fibQuotient
        count += 1
    print(f"OK: definitions match known Pisano periods; all statements hold for m <= 300 "
          f"and for {count} primes p < 3000 (p != 2, 5); no WSS prime found there (as expected).")


if __name__ == "__main__":
    main()
