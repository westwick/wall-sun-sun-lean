import WSS.Frobenius

/-!
# Wall's theorem: `p² ∣ F(p − (p/5)) ↔ π(p²) = π(p)`

This file contains the definition of Wall–Sun–Sun primes and the formal proof of the
equivalence observed by D. D. Wall (1960), together with the dichotomy `π(p²) ∈ {π(p), p π(p)}`.

Sources. Statements follow Wall, *Fibonacci series modulo m*, Amer. Math. Monthly 67 (1960)
525–532, as summarised in J. Klaška, *Donald Dines Wall's conjecture*, Fibonacci Quart. 56
(2018) 43–51 (Wall's paper itself was not consulted directly). Wall writes `k(m)` for `π(m)`.

Main results:
* `isFibPeriod_sq_of`: lifting a period from `p` to `p²` (for odd primes `p`).
* `pisano_sq_dvd`, `pisano_sq_eq_or`: `π(p²) ∣ p π(p)`, hence `π(p²) = π(p)` or
  `π(p²) = p π(p)` (Wall 1960; the case `e = 2` of his prime-power theorem).
* `wall_equivalence`: for a prime `p ≠ 2, 5`, `p² ∣ F(p − (p/5)) ↔ π(p²) = π(p)`.
* `isWallSunSunPrime_iff_pisano`, `isWallSunSunPrime_iff_fibQuotient`: the same statement
  phrased with the definitions `IsWallSunSunPrime` and `fibQuotient`.
-/

namespace WSS

open Nat

/-- A **Wall–Sun–Sun prime**: a prime `p ≠ 2, 5` with `p² ∣ F(p − (p/5))`. -/
def IsWallSunSunPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ p ^ 2 ∣ fib (wallIndex p)

/-- The **Fibonacci quotient** `F(p − (p/5)) / p mod p`. (For primes `p ≠ 2, 5` the division is
exact by `prime_dvd_fib_wallIndex`.) -/
def fibQuotient (p : ℕ) : ZMod p := ((fib (wallIndex p) / p : ℕ) : ZMod p)

/-- **Lifting lemma.** Let `p` be an odd prime. If `p² ∣ F(a)` and `F(a+1) ≡ 1 (mod p)` then
`F(a+1) ≡ 1 (mod p²)`, i.e. `a` is a period modulo `p²`.
Proof: `c = F(a+1)` satisfies `c⁴ ≡ 1 (mod p²)` by Cassini; writing `c = 1 + pt`,
`c⁴ ≡ 1 + 4pt (mod p²)`, so `p ∣ 4t`, so `p ∣ t`. -/
theorem isFibPeriod_sq_of {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h0 : p ^ 2 ∣ fib a)
    (h1 : (fib (a + 1) : ZMod p) = 1) : IsFibPeriod (p ^ 2) a := by
  have h0' : (fib a : ZMod (p ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h0
  refine ⟨h0', ?_⟩
  have h4 := fib_succ_pow_four_of_fib_eq_zero h0'
  set C : ℤ := (fib (a + 1) : ℤ) with hC
  have hd1 : (p : ℤ) ∣ C - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast [hC]; rw [h1]; ring
  have hd4 : ((p ^ 2 : ℕ) : ℤ) ∣ C ^ 4 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast [hC]; rw [h4]; ring
  obtain ⟨t, ht⟩ := hd1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpt : (p : ℤ) ∣ t := by
    have e : C ^ 4 - 1 =
        (p : ℤ) * (4 * t) + (p : ℤ) ^ 2 * (6 * t ^ 2 + 4 * p * t ^ 3 + p ^ 2 * t ^ 4) := by
      rw [show C = p * t + 1 by linear_combination ht]; ring
    rw [e] at hd4
    push_cast at hd4
    have h' : (p : ℤ) * p ∣ p * (4 * t) := by
      rw [← sq]; exact (dvd_add_left (dvd_mul_right _ _)).mp hd4
    have h'' := (mul_dvd_mul_iff_left hp0).mp h'
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h'' with h4 | h4
    · exfalso
      have : p ∣ 2 ^ 2 := by exact_mod_cast h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    · exact h4
  obtain ⟨s, hs⟩ := hpt
  have hfin : ((p ^ 2 : ℕ) : ℤ) ∣ C - 1 := ⟨s, by rw [ht, hs]; push_cast; ring⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hfin
  push_cast [hC] at hfin
  exact sub_eq_zero.mp hfin

/-- **Wall (1960)**: `π(p²) ∣ p · π(p)` for every odd prime `p`. -/
theorem pisano_sq_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : pisano (p ^ 2) ∣ p * pisano p := by
  have hn := isFibPeriod_pisano hp.ne_zero
  apply (isFibPeriod_iff_pisano_dvd (pow_ne_zero 2 hp.ne_zero)).mp
  apply isFibPeriod_sq_of hp hp2
  · exact sq_dvd_fib_mul hp ((ZMod.natCast_eq_zero_iff _ _).mp hn.1)
  · rw [fib_mul_add_of_fib_eq_zero hn.1, hn.2]; simp

/-- `π(p) ∣ π(p²)` for every prime `p`. -/
theorem pisano_dvd_pisano_sq {p : ℕ} (hp : p.Prime) : pisano p ∣ pisano (p ^ 2) :=
  pisano_dvd_pisano (pow_ne_zero 2 hp.ne_zero) (dvd_pow_self p two_ne_zero)

/-- **Wall (1960)**: for an odd prime `p`, either `π(p²) = π(p)` or `π(p²) = p · π(p)`. -/
theorem pisano_sq_eq_or {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    pisano (p ^ 2) = pisano p ∨ pisano (p ^ 2) = p * pisano p := by
  obtain ⟨j, hj⟩ := pisano_dvd_pisano_sq hp
  have hpos := pisano_pos hp.ne_zero
  have hd := pisano_sq_dvd hp hp2
  rw [hj, mul_comm p] at hd
  have hjp : j ∣ p := (Nat.mul_dvd_mul_iff_left hpos).mp hd
  rcases (Nat.dvd_prime hp).mp hjp with rfl | rfl
  · left; rw [hj, mul_one]
  · right; rw [hj, mul_comm]

section main

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_wallIndex : Nat.Coprime p (wallIndex p) := by
  have h2 := hp.out.two_le
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  unfold wallIndex
  split_ifs
  · intro h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · intro h
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h
    exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_one this)

/-- `p ∤ π(p)` for a prime `p ≠ 2, 5` (since `π(p) ∣ 4(p − (p/5))`). -/
theorem not_dvd_pisano (hp2 : p ≠ 2) (hp5 : p ≠ 5) : ¬ p ∣ pisano p := by
  intro h
  have h4 := (h.trans (pisano_dvd_four_mul hp.out.ne_zero (prime_dvd_fib_wallIndex p hp2 hp5)))
  rcases (Nat.Prime.dvd_mul hp.out).mp h4 with h4 | h4
  · have : p ∣ 2 ^ 2 := h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
      (hp.out.dvd_of_dvd_pow this))
  · exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp (coprime_wallIndex) h4

/-- **Wall's theorem** (Wall 1960; see Klaška 2018). For a prime `p ≠ 2, 5`,
`p² ∣ F(p − (p/5))` if and only if the Pisano period modulo `p²` equals the Pisano period
modulo `p`. -/
theorem wall_equivalence (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    p ^ 2 ∣ fib (wallIndex p) ↔ pisano (p ^ 2) = pisano p := by
  set N := wallIndex p
  have hpN : p ∣ fib N := prime_dvd_fib_wallIndex p hp2 hp5
  have hcopN : Nat.Coprime p N := coprime_wallIndex
  have hp20 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.out.ne_zero
  set n := pisano p with hn_def
  have hn := isFibPeriod_pisano hp.out.ne_zero
  rw [← hn_def] at hn
  constructor
  · intro h
    have h1 : p ^ 2 ∣ fib (p * n) :=
      sq_dvd_fib_mul hp.out ((ZMod.natCast_eq_zero_iff _ _).mp hn.1)
    have h2 : p ^ 2 ∣ fib (Nat.gcd (p * n) N) := by
      rw [Nat.fib_gcd]; exact Nat.dvd_gcd h1 h
    rw [Nat.Coprime.gcd_mul_left_cancel n hcopN] at h2
    have h3 : p ^ 2 ∣ fib n := h2.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_left n N))
    have hper : IsFibPeriod (p ^ 2) n := isFibPeriod_sq_of hp.out hp2 h3 hn.2
    exact Nat.dvd_antisymm ((isFibPeriod_iff_pisano_dvd hp20).mp hper)
      (pisano_dvd_pisano_sq hp.out)
  · intro h
    have h3 : p ^ 2 ∣ fib n := by
      have := (isFibPeriod_pisano hp20).1
      rw [h] at this
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    have h1 : p ^ 2 ∣ fib (p * N) := sq_dvd_fib_mul hp.out hpN
    have h2 : p ^ 2 ∣ fib (Nat.gcd n (p * N)) := by
      rw [Nat.fib_gcd]; exact Nat.dvd_gcd h3 h1
    have hcopn : Nat.Coprime p n :=
      (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (not_dvd_pisano hp2 hp5)
    rw [Nat.Coprime.gcd_mul_left_cancel_right N hcopn] at h2
    exact h2.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_right n N))

/-- Wall's theorem phrased with the definition of a Wall–Sun–Sun prime. -/
theorem isWallSunSunPrime_iff_pisano (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    IsWallSunSunPrime p ↔ pisano (p ^ 2) = pisano p := by
  rw [← wall_equivalence hp2 hp5]
  exact ⟨fun h ↦ h.2.2.2, fun h ↦ ⟨hp.out, hp2, hp5, h⟩⟩

/-- A prime `p ≠ 2, 5` is Wall–Sun–Sun iff its Fibonacci quotient vanishes. -/
theorem isWallSunSunPrime_iff_fibQuotient (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    IsWallSunSunPrime p ↔ fibQuotient p = 0 := by
  obtain ⟨q, hq⟩ := prime_dvd_fib_wallIndex p hp2 hp5
  have hp0 := hp.out.pos
  unfold IsWallSunSunPrime fibQuotient
  rw [hq, Nat.mul_div_cancel_left q hp0, ZMod.natCast_eq_zero_iff, sq]
  constructor
  · exact fun h ↦ (Nat.mul_dvd_mul_iff_left hp0).mp h.2.2.2
  · exact fun h ↦ ⟨hp.out, hp2, hp5, Nat.mul_dvd_mul_left p h⟩

/-- Equivalently: a prime `p ≠ 2, 5` is **not** Wall–Sun–Sun iff `π(p²) = p · π(p)`. -/
theorem not_isWallSunSunPrime_iff (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ¬ IsWallSunSunPrime p ↔ pisano (p ^ 2) = p * pisano p := by
  rw [isWallSunSunPrime_iff_pisano hp2 hp5]
  have hpos := pisano_pos hp.out.ne_zero
  rcases pisano_sq_eq_or hp.out hp2 with h | h
  · rw [h]
    constructor
    · intro hne; exact absurd rfl hne
    · intro heq
      have : 1 * pisano p = p * pisano p := by rw [one_mul]; exact heq
      exact absurd (Nat.eq_of_mul_eq_mul_right hpos this).symm hp.out.one_lt.ne'
  · rw [h]
    constructor
    · intro _; rfl
    · intro _ heq
      have : p * pisano p = 1 * pisano p := by rw [one_mul]; exact heq
      exact hp.out.one_lt.ne' (Nat.eq_of_mul_eq_mul_right hpos this)

end main

end WSS
