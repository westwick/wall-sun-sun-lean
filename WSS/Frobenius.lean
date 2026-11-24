import WSS.Pisano

/-!
# `p ∣ F(p − (p/5))`: the Fibonacci numbers at a prime, via Frobenius

For a prime `p ≠ 2, 5` we compute `F(p)` and `F(p − 1)` modulo `p` exactly:

* `F(p)     ≡ (5/p)            (mod p)`
* `2 F(p−1) ≡ 1 − (5/p)        (mod p)`

where `(5/p)` is the Legendre symbol. Consequently `p ∣ F(p − 1)` if `(5/p) = 1` and
`p ∣ F(p + 1)` if `(5/p) = −1`. By quadratic reciprocity `(5/p) = (p/5)`, which gives the
classical statement `p ∣ F(p − (p/5))` (Lucas 1878; Wall 1960 quotes it as known).

The proof is the matrix form of the usual argument in `𝔽_p[√5]`. With `Q = [[1,1],[1,0]]` we
have `Q^(n+1) = [[F(n+2), F(n+1)], [F(n+1), F(n)]]`, and `2Q = S + 1` with `S = [[1,2],[2,−1]]`,
`S² = 5`. In characteristic `p`, since `S` and `1` commute, `(S + 1)^p = S^p + 1`, and
`S^p = (S²)^((p−1)/2) S = 5^((p−1)/2) S = (5/p) S` by Euler's criterion. Comparing entries of
`2^p Q^p = (5/p) S + 1` gives the two congruences above.

Main results:
* `fib_prime_zmod`, `two_mul_fib_prime_sub_one_zmod`: the two congruences.
* `prime_dvd_fib_wallIndex`: `p ∣ F(p − (p/5))`.
* `isFibPeriod_prime`: `p − 1` (if `(p/5) = 1`) or `2(p + 1)` (if `(p/5) = −1`) is a period
  modulo `p`; hence `π(p) ∣ p − 1` or `π(p) ∣ 2(p + 1)` (Wall 1960).
-/

namespace WSS

open Nat Matrix

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- **Wall's index** `p − (p/5)`, where `(p/5)` is the Legendre symbol. For `p = 5` (where the
symbol is `0`) this convention gives `6`; we only use it for `p ≠ 5`. -/
def wallIndex (p : ℕ) : ℕ :=
  if legendreSym 5 (p : ℤ) = 1 then p - 1 else p + 1

/-- The Fibonacci `Q`-matrix. -/
def fibQ (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, 0]

/-- `Q^(n+1) = [[F(n+2), F(n+1)], [F(n+1), F(n)]]`. -/
theorem fibQ_pow_succ (R : Type*) [CommRing R] (n : ℕ) :
    fibQ R ^ (n + 1) = !![(fib (n + 2) : R), fib (n + 1); fib (n + 1), fib n] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [fibQ]
  | succ n ih =>
    rw [pow_succ, ih]
    have e1 := fib_add_two_cast (R := R) n
    have e2 := fib_add_two_cast (R := R) (n + 1)
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [fibQ, Matrix.mul_apply, Fin.sum_univ_two, e1, e2] <;> ring

/-- `Q^n = [[F(n+1), F(n)], [F(n), F(n−1)]]` for `n ≥ 1`. -/
theorem fibQ_pow (R : Type*) [CommRing R] {n : ℕ} (hn : 0 < n) :
    fibQ R ^ n = !![(fib (n + 1) : R), fib n; fib n, fib (n - 1)] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [fibQ_pow_succ, Nat.add_sub_cancel]

section prime

variable (p : ℕ) [hp : Fact p.Prime]

/-- `S = 2Q − 1`. -/
def fibS : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 2; 2, -1]

theorem two_smul_fibQ : (2 : ZMod p) • fibQ (ZMod p) = fibS p + 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [fibQ, fibS]; norm_num

theorem fibS_sq : fibS p ^ 2 = (5 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [fibS, sq, Matrix.mul_apply] <;> norm_num

/-- The Frobenius identity `2 Q^p = 5^((p−1)/2) S + 1` over `𝔽_p`. -/
theorem two_smul_fibQ_pow (hp2 : p ≠ 2) :
    (2 : ZMod p) • fibQ (ZMod p) ^ p = (5 : ZMod p) ^ (p / 2) • fibS p + 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have h1 : ((2 : ZMod p) • fibQ (ZMod p)) ^ p = (2 : ZMod p) • fibQ (ZMod p) ^ p := by
    rw [smul_pow, ZMod.pow_card]
  rw [← h1, two_smul_fibQ, add_pow_char_of_commute p (Commute.one_right _), one_pow]
  congr 1
  have hpe : fibS p ^ p = fibS p ^ (2 * (p / 2) + 1) := by congr 1; omega
  rw [hpe, pow_succ, pow_mul, fibS_sq, smul_pow, one_pow]
  rw [smul_mul_assoc, one_mul]

theorem five_ne_zero (hp5 : p ≠ 5) : ((5 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp5 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_five).mp this)

/-- **Euler + Frobenius**: `F(p) ≡ (5/p) (mod p)` for every odd prime `p`. -/
theorem fib_prime_zmod (hp2 : p ≠ 2) : (fib p : ZMod p) = legendreSym p 5 := by
  have h := congrArg (fun A ↦ A 0 1) (two_smul_fibQ_pow p hp2)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  rw [legendreSym.eq_pow]
  simp only [fibQ_pow _ hp.out.pos] at h
  simp [fibS] at h
  push_cast
  apply mul_left_cancel₀ h2
  linear_combination h

/-- **Euler + Frobenius**: `2 F(p−1) ≡ 1 − (5/p) (mod p)` for every odd prime `p`. -/
theorem two_mul_fib_prime_sub_one_zmod (hp2 : p ≠ 2) :
    2 * (fib (p - 1) : ZMod p) = 1 - legendreSym p 5 := by
  have h := congrArg (fun A ↦ A 1 1) (two_smul_fibQ_pow p hp2)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  rw [legendreSym.eq_pow]
  simp only [fibQ_pow _ hp.out.pos] at h
  simp [fibS] at h
  push_cast
  linear_combination h

theorem legendreSym_five_eq (hp2 : p ≠ 2) : legendreSym p 5 = legendreSym 5 p :=
  legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hp2

/-- `(p/5) = ±1` for a prime `p ≠ 5`. -/
theorem legendreSym_five_eq_one_or_neg_one (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    legendreSym 5 p = 1 ∨ legendreSym 5 p = -1 := by
  rw [← legendreSym_five_eq p hp2]
  exact legendreSym.eq_one_or_neg_one p (five_ne_zero p hp5)

/-- `(p/5) = 1` iff `p ≡ ±1 (mod 5)` (and otherwise, for `5 ∤ p`, `(p/5) = −1`). -/
theorem legendreSym_five_eq_one_iff {p : ℕ} (hp5 : ¬ 5 ∣ p) :
    legendreSym 5 p = 1 ↔ p % 5 = 1 ∨ p % 5 = 4 := by
  rw [legendreSym.mod 5 (p : ℤ), show (p : ℤ) % ((5 : ℕ) : ℤ) = ((p % 5 : ℕ) : ℤ) by
    push_cast; rfl]
  have h5 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h0 : p % 5 ≠ 0 := fun h ↦ hp5 (Nat.dvd_of_mod_eq_zero h)
  generalize p % 5 = r at h5 h0 ⊢
  interval_cases r <;> norm_num

/-- `wallIndex p = p − (p/5)` as integers, for primes `p ≠ 2, 5`. -/
theorem wallIndex_eq (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (wallIndex p : ℤ) = p - legendreSym 5 p := by
  unfold wallIndex
  rcases legendreSym_five_eq_one_or_neg_one p hp2 hp5 with h | h
  · simp only [h, ↓reduceIte]; push_cast [hp.out.one_le]; ring
  · rw [h]; simp only [show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte]; push_cast; ring

/-- The two cases: `F(p−1) ≡ 0, F(p) ≡ 1` when `(p/5) = 1`, and
`F(p+1) ≡ 0, F(p+2) ≡ −1` when `(p/5) = −1`. -/
theorem fib_prime_cases (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (legendreSym 5 p = 1 ∧ (fib (p - 1) : ZMod p) = 0 ∧ (fib p : ZMod p) = 1) ∨
    (legendreSym 5 p = -1 ∧ (fib (p + 1) : ZMod p) = 0 ∧ (fib (p + 2) : ZMod p) = -1) := by
  have hF := fib_prime_zmod p hp2
  have hG := two_mul_fib_prime_sub_one_zmod p hp2
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  rw [legendreSym_five_eq p hp2] at hF hG
  have hp1 := hp.out.one_le
  have e1 := fib_add_two_cast (R := ZMod p) (p - 1)
  have e2 := fib_add_two_cast (R := ZMod p) p
  rw [show p - 1 + 2 = p + 1 by omega, show p - 1 + 1 = p by omega] at e1
  rcases legendreSym_five_eq_one_or_neg_one p hp2 hp5 with h | h
  · left
    rw [h] at hF hG
    refine ⟨h, ?_, by simpa using hF⟩
    exact (_root_.mul_eq_zero.mp (by simpa using hG)).resolve_left h2
  · right
    rw [h] at hF hG
    push_cast at hF hG
    have hq' : (fib (p - 1) : ZMod p) = 1 := mul_left_cancel₀ h2 (by linear_combination hG)
    refine ⟨h, ?_, ?_⟩
    · rw [e1, hq', hF]; ring
    · rw [e2, e1, hq', hF]; ring

/-- **`p ∣ F(p − (p/5))`** for every prime `p ≠ 2, 5`. -/
theorem prime_dvd_fib_wallIndex (hp2 : p ≠ 2) (hp5 : p ≠ 5) : p ∣ fib (wallIndex p) := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold wallIndex
  rcases fib_prime_cases p hp2 hp5 with ⟨h, h0, -⟩ | ⟨h, h0, -⟩
  · simp only [h, ↓reduceIte]; exact h0
  · simp only [h, show (-1 : ℤ) ≠ 1 by decide, ↓reduceIte]; exact h0

/-- **Wall (1960)**: if `(p/5) = 1` then `p − 1` is a period modulo `p`; if
`(p/5) = −1` then `2(p + 1)` is a period modulo `p`. -/
theorem isFibPeriod_prime (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (legendreSym 5 p = 1 ∧ IsFibPeriod p (p - 1)) ∨
    (legendreSym 5 p = -1 ∧ IsFibPeriod p (2 * (p + 1))) := by
  rcases fib_prime_cases p hp2 hp5 with ⟨h, h0, h1⟩ | ⟨h, h0, h1⟩
  · left
    refine ⟨h, h0, ?_⟩
    rwa [Nat.sub_add_cancel hp.out.one_le]
  · right
    refine ⟨h, ?_⟩
    rw [isFibPeriod_iff_forall]
    intro n
    rw [fib_mul_add_of_fib_eq_zero h0, show p + 1 + 1 = p + 2 by ring, h1]
    ring

/-- `π(p) ∣ p − 1` if `(p/5) = 1`, and `π(p) ∣ 2(p + 1)` if `(p/5) = −1`. -/
theorem pisano_prime_dvd (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (legendreSym 5 p = 1 ∧ pisano p ∣ p - 1) ∨
    (legendreSym 5 p = -1 ∧ pisano p ∣ 2 * (p + 1)) := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  rcases isFibPeriod_prime p hp2 hp5 with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact Or.inl ⟨h, (isFibPeriod_iff_pisano_dvd hp0).mp h'⟩
  · exact Or.inr ⟨h, (isFibPeriod_iff_pisano_dvd hp0).mp h'⟩

end prime

end WSS
