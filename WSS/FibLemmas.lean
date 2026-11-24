import Mathlib

/-!
# Fibonacci identities in an arbitrary commutative ring

Elementary identities for the images `(fib n : R)` of the Fibonacci numbers in a commutative
ring `R` (typically `R = ZMod m`). These are the algebraic engine behind everything else.

Main results:
* `WSS.fib_add_of_fib_eq_zero`: if `F(a) = 0` in `R` then `F(a + n) = F(a+1) F(n)`.
* `WSS.fib_mul_add_of_fib_eq_zero`: under the same hypothesis, `F(k a + n) = F(a+1)^k F(n)`.
* `WSS.cassini`: Cassini's identity `F(n+2) F(n) - F(n+1)^2 = (-1)^(n+1)`.
* `WSS.fib_succ_sq_of_fib_eq_zero`: if `F(a) = 0` in `R` then `F(a+1)^2 = (-1)^a`.
* `WSS.sq_dvd_fib_mul`: if a prime `p` divides `F(a)` then `p^2` divides `F(p a)`.
-/

namespace WSS

open Nat

variable {R : Type*} [CommRing R]

/-- Mathlib's addition formula, cast into any commutative ring. -/
theorem fib_add_cast (a n : ℕ) :
    (fib (a + n + 1) : R) = fib a * fib n + fib (a + 1) * fib (n + 1) := by
  rw [fib_add]; push_cast; ring

/-- The recurrence, cast into any commutative ring. -/
theorem fib_add_two_cast (n : ℕ) : (fib (n + 2) : R) = fib n + fib (n + 1) := by
  rw [fib_add_two]; push_cast; ring

/-- If `F(a)` vanishes in `R`, then shifting by `a` multiplies by `F(a+1)`. -/
theorem fib_add_of_fib_eq_zero {a : ℕ} (ha : (fib a : R) = 0) (n : ℕ) :
    (fib (a + n) : R) = fib (a + 1) * fib n := by
  cases n with
  | zero => simp [ha]
  | succ n => rw [← add_assoc, fib_add_cast, ha]; ring

/-- If `F(a)` vanishes in `R`, then `F(k a + n) = F(a+1)^k F(n)` in `R`. -/
theorem fib_mul_add_of_fib_eq_zero {a : ℕ} (ha : (fib a : R) = 0) (k n : ℕ) :
    (fib (k * a + n) : R) = fib (a + 1) ^ k * fib n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * a + n = a + (k * a + n) by ring, fib_add_of_fib_eq_zero ha, ih]
    ring

/-- **Cassini's identity** (over `ℤ`): `F(n+2) F(n) - F(n+1)^2 = (-1)^(n+1)`. -/
theorem cassini_int (n : ℕ) :
    (fib (n + 2) * fib n : ℤ) - fib (n + 1) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (fib (n + 3) : ℤ) = fib (n + 1) + fib (n + 2) := fib_add_two_cast (n + 1)
    have h2 : (fib (n + 2) : ℤ) = fib n + fib (n + 1) := fib_add_two_cast n
    rw [h1]
    linear_combination -ih - (fib (n + 2) : ℤ) * h2

/-- **Cassini's identity** in any commutative ring. -/
theorem cassini (n : ℕ) :
    (fib (n + 2) * fib n : R) - fib (n + 1) ^ 2 = (-1) ^ (n + 1) := by
  have := congrArg (Int.cast : ℤ → R) (cassini_int n)
  push_cast at this
  exact this

/-- If `F(a)` vanishes in `R` then `F(a+1)^2 = (-1)^a` in `R`. -/
theorem fib_succ_sq_of_fib_eq_zero {a : ℕ} (ha : (fib a : R) = 0) :
    (fib (a + 1) : R) ^ 2 = (-1) ^ a := by
  cases a with
  | zero => simp
  | succ b =>
    have hc := cassini (R := R) b
    have h2 := fib_add_two_cast (R := R) b
    rw [ha] at h2 hc
    rw [h2] at hc ⊢
    linear_combination hc

/-- If `F(a)` vanishes in `R` then `F(a+1)^4 = 1` in `R`. -/
theorem fib_succ_pow_four_of_fib_eq_zero {a : ℕ} (ha : (fib a : R) = 0) :
    (fib (a + 1) : R) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, fib_succ_sq_of_fib_eq_zero ha, ← pow_mul, mul_comm,
    pow_mul]
  simp

/-- Auxiliary: `F(k a + 1) ≡ F(a+1)^k` modulo `F(a)`, as an exact identity in `R`
with an explicit (existential) multiple of `F(a)`. -/
theorem fib_mul_add_one_eq (a k : ℕ) :
    ∃ y : R, (fib (k * a + 1) : R) = fib (a + 1) ^ k + fib a * y := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨fib (k * a) + y * fib (a + 1), ?_⟩
    rw [show (k + 1) * a + 1 = k * a + a + 1 by ring, fib_add_cast, hy]
    ring

/-- Auxiliary: if `F(a)^2 = 0` in `R` then `F((k+1) a) = (k+1) F(a+1)^k F(a)` in `R`. -/
theorem fib_succ_mul_eq_of_sq_eq_zero {a : ℕ} (ha : 0 < a) (hsq : (fib a : R) ^ 2 = 0)
    (k : ℕ) : (fib ((k + 1) * a) : R) = (k + 1) * fib (a + 1) ^ k * fib a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨y, hy⟩ := fib_mul_add_one_eq (R := R) (b + 1) (k + 1)
    have h2 := fib_add_two_cast (R := R) b
    rw [show (k + 1 + 1) * (b + 1) = (k + 1) * (b + 1) + b + 1 by ring, fib_add_cast, ih, hy]
    have hb : (fib b : R) = fib (b + 2) - fib (b + 1) := by rw [h2]; ring
    rw [hb]
    push_cast
    linear_combination (-(k + 1 : R) * fib (b + 1 + 1) ^ k + y) * hsq

/-- `p^2 = 0` in `ZMod (p^2)`. -/
theorem natCast_sq_eq_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- If a prime `p` divides `F(a)`, then `p^2` divides `F(p a)`. -/
theorem sq_dvd_fib_mul {p a : ℕ} (hp : p.Prime) (h : p ∣ fib a) : p ^ 2 ∣ fib (p * a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  obtain ⟨u, hu⟩ := h
  have hsq : (fib a : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [hu]; push_cast; rw [mul_pow, natCast_sq_eq_zero, zero_mul]
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have key := fib_succ_mul_eq_of_sq_eq_zero ha hsq q
  rw [← hq] at key
  rw [← ZMod.natCast_eq_zero_iff, key, hu]
  have : ((q : ZMod (p ^ 2)) + 1) = p := by rw [hq]; push_cast; ring
  rw [this]
  push_cast
  linear_combination (fib (a + 1) : ZMod (p ^ 2)) ^ q * u * natCast_sq_eq_zero p

end WSS
