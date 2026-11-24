# Lean 4 formalization: Wall's theorem on Fibonacci periods

A machine-checked proof, in Lean 4 with Mathlib, of D. D. Wall's 1960 theorem connecting
Wall–Sun–Sun primes to Pisano periods: for a prime `p ≠ 2, 5`,
`p² ∣ F(p − (p/5))` if and only if `π(p²) = π(p)`.

This is the formalization part of a larger research project on Wall–Sun–Sun primes by
Andrew Westwick.

Lean 4.37.0-rc1 + Mathlib v4.37.0-rc1. About 800 lines in `WSS/`.

**Status: everything listed under "Proved" below is PROVEN.** It compiles with no `sorry`,
no `native_decide` and no added axioms. Each theorem depends only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). The script `scripts/Axioms.lean` prints
this for every headline theorem.

## How to check

```bash
lake exe cache get                 # download prebuilt Mathlib
lake build                          # builds everything; should print "Build completed successfully"
lake env lean scripts/Axioms.lean   # each line should end in [propext, Classical.choice, Quot.sound]
python3 scripts/check_definitions.py   # independent numerical check of every statement (about 45 s)
```

## Plain English

The Fibonacci numbers 0, 1, 1, 2, 3, 5, 8, … repeat in a cycle once you keep only their
remainders after dividing by a fixed number m. The length of that cycle is the
**Pisano period π(m)**. For example, the remainders mod 7 repeat every 16 steps, so π(7) = 16.

In 1960 D. D. Wall asked whether the cycle mod p² is always longer than the cycle mod p, for
every prime p. He also noted that the cycle fails to get longer exactly when p² divides a
particular Fibonacci number, F(p − 1) or F(p + 1), depending on p's last digit. Primes where
that happens are now called **Wall–Sun–Sun primes**. None are known.

We wrote that equivalence and the facts it rests on in Lean, and Lean checked every logical
step from the basic axioms. The most important results are:

1. **The Fibonacci sequence mod m is periodic.** The repeat lengths are exactly the multiples
   of π(m), and π(m) is even when m > 2.
2. **Every prime p ≠ 2, 5 divides F(p − 1) or F(p + 1).** It divides F(p − 1) if p ends in 1
   or 9, and F(p + 1) if p ends in 3 or 7. As a consequence, π(p) divides p − 1 or
   2(p + 1).
3. **Going from p to p² multiplies the cycle length by exactly 1 or p.** No other factor is
   possible.
4. **Wall's theorem.** p² divides that Fibonacci number exactly when the cycle mod p² has
   the same length as the cycle mod p.
5. **Wall's question has answer "yes" exactly when no Wall–Sun–Sun primes exist.** This holds
   for all primes, including 2 and 5, which are checked separately.

As far as we can tell, none of this had been machine-checked before. Mathlib, Lean's main
mathematics library, has Fibonacci numbers, Cassini's identity, gcd(F(a), F(b)) = F(gcd(a, b))
and quadratic reciprocity. It has no Pisano period and none of Wall's results. Web searches
for Lean, Isabelle or Coq formalizations of Pisano periods or Wall–Sun–Sun primes found
nothing.

## Definitions (`WSS/Pisano.lean`, `WSS/Frobenius.lean`, `WSS/Wall.lean`)

| Lean name | Meaning |
|---|---|
| `IsFibPeriod m k` | `F(k) ≡ 0` and `F(k+1) ≡ 1 (mod m)` (equivalently `F(n+k) ≡ F(n)` for all `n`: `isFibPeriod_iff_forall`) |
| `pisano m` | least positive `k` with `IsFibPeriod m k` (and `pisano 0 = 0`) |
| `wallIndex p` | `p − 1` if the Legendre symbol `(p/5) = 1`, else `p + 1`; equals `p − (p/5)` for primes `p ≠ 2, 5` (`wallIndex_eq`) |
| `IsWallSunSunPrime p` | `p` prime, `p ≠ 2, 5`, and `p² ∣ F(wallIndex p)` |
| `fibQuotient p` | `F(p − (p/5)) / p` reduced mod `p`, in `ZMod p` |

Here `(p/5)` is Mathlib's `legendreSym 5 p`, and Mathlib's `Nat.fib` is the Fibonacci
sequence with `F(0) = 0` and `F(1) = 1`.

## Proved

Sources: Wall 1960 (Amer. Math. Monthly 67, 525–532), as summarized in Klaška 2018
(Fibonacci Quart. 56, 43–51). We did not see Wall's paper itself (JSTOR), so attributions to Wall
come from secondary sources and should be checked against the original. The statements themselves are exact and self-contained.

| Lean theorem | Statement | Classical source |
|---|---|---|
| `exists_isFibPeriod` | for `m ≠ 0` a positive period exists | Wall 1960 |
| `isFibPeriod_iff_pisano_dvd` | `k` is a period mod `m` ⇔ `π(m) ∣ k` | standard |
| `pisano_dvd_pisano` | `d ∣ m ⇒ π(d) ∣ π(m)` | Wall 1960 |
| `even_pisano` | `m > 2 ⇒ π(m)` even | Wall 1960 |
| `pisano_dvd_four_mul` | `m ∣ F(a) ⇒ π(m) ∣ 4a` | standard (π/α ∈ {1,2,4}) |
| `cassini` | `F(n+2)F(n) − F(n+1)² = (−1)^(n+1)` in any commutative ring | Cassini |
| `sq_dvd_fib_mul` | `p` prime, `p ∣ F(a) ⇒ p² ∣ F(pa)` | Lucas |
| `fib_prime_zmod` | `F(p) ≡ (5/p) (mod p)`, `p` odd prime | Lucas 1878 |
| `two_mul_fib_prime_sub_one_zmod` | `2F(p−1) ≡ 1 − (5/p) (mod p)` | Lucas 1878 |
| `legendreSym_five_eq_one_iff` | `(p/5) = 1 ⇔ p ≡ ±1 (mod 5)` (for `5 ∤ p`) | |
| `prime_dvd_fib_wallIndex` | `p ≠ 2, 5` prime ⇒ `p ∣ F(p − (p/5))` | Lucas 1878 |
| `pisano_prime_dvd` | `π(p) ∣ p − 1` if `(p/5) = 1`; `π(p) ∣ 2(p+1)` if `(p/5) = −1` | Wall 1960 |
| `not_dvd_pisano` | `p ≠ 2, 5 ⇒ p ∤ π(p)` | |
| `isFibPeriod_sq_of` | `p` odd, `p² ∣ F(a)`, `F(a+1) ≡ 1 (mod p) ⇒ F(a+1) ≡ 1 (mod p²)` | lifting lemma |
| `pisano_sq_dvd` | `p` odd prime ⇒ `π(p²) ∣ p·π(p)` | Wall 1960 |
| `pisano_sq_eq_or` | `π(p²) = π(p)` or `π(p²) = p·π(p)` | Wall 1960 |
| **`wall_equivalence`** | **`p ≠ 2, 5` prime: `p² ∣ F(p − (p/5)) ⇔ π(p²) = π(p)`** | **Wall 1960** |
| `isWallSunSunPrime_iff_pisano` | `IsWallSunSunPrime p ⇔ π(p²) = π(p)` | |
| `isWallSunSunPrime_iff_fibQuotient` | `IsWallSunSunPrime p ⇔ fibQuotient p = 0` | |
| `not_isWallSunSunPrime_iff` | not WSS ⇔ `π(p²) = p·π(p)` | |
| `wallQuestion_iff_noWallSunSunPrimes` | Wall's question (`π(p²) ≠ π(p)` for all primes) ⇔ no WSS primes | |

`WSS/Examples.lean` checks small cases inside Lean: π(2) = 3, π(5) = 20, π(7) = 16,
π(10) = 60, π(11) = 10, 7 is not a WSS prime, and therefore π(49) = 112.

## Stated only (not proved)

- `SunSunStatement` (`WSS/Statements.lean`): Sun & Sun 1992. A counterexample to the first
  case of Fermat's Last Theorem for exponent p forces p to be a WSS prime. This is recorded
  as a `Prop`, not as an axiom, so no proved result depends on it.

## How the proofs go (for mathematicians)

- **Ring identities** (`FibLemmas.lean`). Suppose `F(a) = 0` in a commutative ring `R`. Then
  `F(ka + n) = F(a+1)^k F(n)` and `F(a+1)² = (−1)^a` (from Cassini), so `F(a+1)^4 = 1`.
  Also, if `F(a)² = 0` then `F((k+1)a) = (k+1) F(a+1)^k F(a)`. Applying this in `ZMod p²`
  gives `p ∣ F(a) ⇒ p² ∣ F(pa)`.
- **Periodicity** (`Pisano.lean`). Pigeonhole on the pairs `(F(n), F(n+1)) mod m`, followed
  by running the recurrence backwards. The set of periods is closed under addition and
  under truncated subtraction, so it is exactly the set of multiples of `π(m)`.
- **`p ∣ F(p − (p/5))`** (`Frobenius.lean`). Work with 2×2 matrices over `𝔽_p`. With
  `Q = [[1,1],[1,0]]` and `S = 2Q − 1`, we have `S² = 5`. Since `S` commutes with `1`,
  `(S + 1)^p = S^p + 1`. Also `S^p = 5^((p−1)/2) S = (5/p) S` by Euler's criterion
  (`legendreSym.eq_pow`). Reading off the entries of `2Q^p = (5/p)S + 1` gives
  `F(p) ≡ (5/p)` and `2F(p−1) ≡ 1 − (5/p)`. Quadratic reciprocity
  (`legendreSym.quadratic_reciprocity_one_mod_four`) turns `(5/p)` into `(p/5)`.
- **Wall's theorem** (`Wall.lean`). Write `N = p − (p/5)` and `n = π(p)`. Note that `p ∤ N`.
  - (⇒) Since `p ∣ F(n)`, we get `p² ∣ F(pn)`. Combined with the hypothesis `p² ∣ F(N)`,
    strong divisibility gives `p² ∣ F(gcd(pn, N)) = F(gcd(n, N))`, which divides `F(n)`.
    Next, `c = F(n+1)` satisfies `c ≡ 1 (mod p)` and `c⁴ ≡ 1 (mod p²)`. Since `p` is odd,
    this forces `c ≡ 1 (mod p²)`, so `n` is a period mod `p²`.
  - (⇐) `π(p) ∣ 4N`, so `p ∤ π(p) = n`. Now `p² ∣ F(n)` and `p² ∣ F(pN)`, so
    `p² ∣ F(gcd(n, pN)) = F(gcd(n, N))`, which divides `F(N)`.

  This route avoids the rank of apparition α(m) entirely.

## Files

- `WSS/FibLemmas.lean`: Fibonacci identities in a commutative ring.
- `WSS/Pisano.lean`: periods, the Pisano period, evenness, and `pisano_eq_of` for computing it.
- `WSS/Frobenius.lean`: `wallIndex`, the Frobenius computation, and `p ∣ F(p − (p/5))`.
- `WSS/Wall.lean`: the WSS definition, the lifting lemma, the dichotomy, and Wall's theorem.
- `WSS/Examples.lean`: small cases checked inside Lean.
- `WSS/Statements.lean`: Wall's question ⇔ no WSS primes (proved), and Sun–Sun (stated only).
- `scripts/Axioms.lean`: axiom audit.
- `scripts/check_definitions.py`: independent numerical check of every statement for `m ≤ 300`
  and for primes `p < 3000`.

## Possible next steps

- Wall's general prime-power result: if `t` is the largest exponent with `π(p^t) = π(p)`, then
  `π(p^e) = p^(e−t) π(p)` for `e ≥ t`. This needs a lifting-the-exponent argument for all
  `e`, generalizing `isFibPeriod_sq_of`.
- `π(lcm(a, b)) = lcm(π(a), π(b))` (Wall 1960).
- The same equivalence for general Lucas sequences (generalized Lucas–Wieferich primes).
- Upstreaming `pisano` and the Frobenius lemmas to Mathlib.
