import WSS.FibLemmas

/-!
# The Pisano period

For a modulus `m ≥ 1`, the Fibonacci sequence reduced mod `m` is periodic. We call `k` a
*Fibonacci period modulo `m`* when `F(k) ≡ 0` and `F(k+1) ≡ 1 (mod m)`; equivalently
`F(n + k) ≡ F(n) (mod m)` for every `n` (`isFibPeriod_iff_forall`). The **Pisano period**
`pisano m` (written `π(m)` or `k(m)` in the literature; Wall 1960 writes `k(m)`) is the least
positive Fibonacci period.

Main results:
* `exists_isFibPeriod`: for `m ≠ 0` a positive period exists (pigeonhole).
* `isFibPeriod_iff_pisano_dvd`: the periods modulo `m` are exactly the multiples of `π(m)`.
* `pisano_dvd_four_mul`: if `m ∣ F(a)` then `π(m) ∣ 4a`.
* `pisano_dvd_pisano`: if `d ∣ m` then `π(d) ∣ π(m)`.
* `even_pisano`: `π(m)` is even for `m > 2` (Wall 1960).
-/

namespace WSS

open Nat

/-- `k` is a **Fibonacci period modulo `m`**: `F(k) ≡ 0` and `F(k+1) ≡ 1 (mod m)`. -/
def IsFibPeriod (m k : ℕ) : Prop :=
  (fib k : ZMod m) = 0 ∧ (fib (k + 1) : ZMod m) = 1

/-- `k` is a period iff shifting by `k` fixes the whole sequence mod `m`. -/
theorem isFibPeriod_iff_forall {m k : ℕ} :
    IsFibPeriod m k ↔ ∀ n, (fib (k + n) : ZMod m) = fib n := by
  constructor
  · rintro ⟨h0, h1⟩ n
    rw [fib_add_of_fib_eq_zero h0, h1, one_mul]
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩

theorem isFibPeriod_zero (m : ℕ) : IsFibPeriod m 0 := by simp [IsFibPeriod]

theorem IsFibPeriod.add {m k l : ℕ} (hk : IsFibPeriod m k) (hl : IsFibPeriod m l) :
    IsFibPeriod m (k + l) := by
  rw [isFibPeriod_iff_forall] at *
  intro n; rw [add_assoc, hk, hl]

theorem IsFibPeriod.mul {m k : ℕ} (hk : IsFibPeriod m k) (q : ℕ) :
    IsFibPeriod m (k * q) := by
  induction q with
  | zero => exact isFibPeriod_zero m
  | succ q ih => rw [mul_add, mul_one]; exact ih.add hk

theorem IsFibPeriod.sub {m k l : ℕ} (hk : IsFibPeriod m k) (hl : IsFibPeriod m l) (hlk : l ≤ k) :
    IsFibPeriod m (k - l) := by
  rw [isFibPeriod_iff_forall] at *
  intro n
  rw [← hl, ← add_assoc, Nat.add_sub_cancel' hlk, hk]

/-- A period modulo `m` is a period modulo any divisor of `m`. -/
theorem IsFibPeriod.of_dvd {d m k : ℕ} (hdm : d ∣ m) (hk : IsFibPeriod m k) :
    IsFibPeriod d k := by
  obtain ⟨h0, h1⟩ := hk
  have h0' := congrArg (ZMod.castHom hdm (ZMod d)) h0
  have h1' := congrArg (ZMod.castHom hdm (ZMod d)) h1
  simp only [map_natCast, map_zero, map_one] at h0' h1'
  exact ⟨h0', h1'⟩

/-- Pairs of consecutive terms: if they agree at `i` and `i + d`, they agree at `0` and `d`. -/
theorem fibPair_descent {m : ℕ} (d : ℕ) :
    ∀ i, ((fib i : ZMod m) = fib (i + d) ∧ (fib (i + 1) : ZMod m) = fib (i + d + 1)) →
      ((fib 0 : ZMod m) = fib d ∧ (fib 1 : ZMod m) = fib (d + 1)) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rintro ⟨h0, h1⟩
    apply ih
    refine ⟨?_, by rw [h0, add_right_comm]⟩
    have e1 := fib_add_two_cast (R := ZMod m) i
    have e2 := fib_add_two_cast (R := ZMod m) (i + d)
    rw [show i + d + 2 = i + 1 + d + 1 by ring, ← h1, show i + 2 = i + 1 + 1 by ring,
      show i + d + 1 = i + 1 + d by ring, ← h0] at e2
    rw [show i + 1 + 1 = i + 2 by ring] at e1
    linear_combination e2 - e1

/-- **Periodicity of the Fibonacci sequence modulo `m`**: for `m ≠ 0` there is a positive
period. Proof by pigeonhole on the finitely many pairs `(F(n), F(n+1)) mod m`. -/
theorem exists_isFibPeriod {m : ℕ} (hm : m ≠ 0) : ∃ k, 0 < k ∧ IsFibPeriod m k := by
  have : NeZero m := ⟨hm⟩
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ ((fib n : ZMod m), (fib (n + 1) : ZMod m)))
  simp only [Prod.mk.injEq] at hfij
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm ⟨hfij.1.symm, hfij.2.symm⟩ (by omega)
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  refine ⟨d, by omega, ?_⟩
  obtain ⟨h0, h1⟩ := fibPair_descent d i hfij
  exact ⟨by simpa using h0.symm, by simpa using h1.symm⟩

/-- The **Pisano period** `π(m)`: the least positive Fibonacci period modulo `m`
(by convention `π(0) = 0`, since the integer Fibonacci sequence is not periodic). -/
noncomputable def pisano (m : ℕ) : ℕ :=
  sInf {k | 0 < k ∧ IsFibPeriod m k}

theorem pisano_spec {m : ℕ} (hm : m ≠ 0) : 0 < pisano m ∧ IsFibPeriod m (pisano m) :=
  Nat.sInf_mem (s := {k | 0 < k ∧ IsFibPeriod m k}) (exists_isFibPeriod hm)

theorem pisano_pos {m : ℕ} (hm : m ≠ 0) : 0 < pisano m := (pisano_spec hm).1

theorem isFibPeriod_pisano {m : ℕ} (hm : m ≠ 0) : IsFibPeriod m (pisano m) :=
  (pisano_spec hm).2

theorem pisano_le {m k : ℕ} (hk : 0 < k) (h : IsFibPeriod m k) : pisano m ≤ k :=
  Nat.sInf_le ⟨hk, h⟩

/-- **The periods modulo `m` are exactly the multiples of the Pisano period.** -/
theorem isFibPeriod_iff_pisano_dvd {m k : ℕ} (hm : m ≠ 0) :
    IsFibPeriod m k ↔ pisano m ∣ k := by
  constructor
  · intro hk
    have hP := isFibPeriod_pisano hm
    have hPpos := pisano_pos hm
    have hr : IsFibPeriod m (k % pisano m) := by
      have := hk.sub (hP.mul (k / pisano m)) (Nat.mul_div_le k _)
      rwa [← Nat.mod_eq_sub_mul_div] at this
    by_contra hdvd
    have hpos : 0 < k % pisano m := Nat.pos_of_ne_zero (fun h ↦ hdvd (Nat.dvd_of_mod_eq_zero h))
    exact absurd (pisano_le hpos hr) (not_le.mpr (Nat.mod_lt _ hPpos))
  · rintro ⟨q, rfl⟩
    exact (isFibPeriod_pisano hm).mul q

/-- If `m ∣ F(a)` then `4a` is a period modulo `m`, so `π(m) ∣ 4a`. -/
theorem isFibPeriod_four_mul {m a : ℕ} (ha : m ∣ fib a) : IsFibPeriod m (4 * a) := by
  have ha' : (fib a : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ha
  rw [isFibPeriod_iff_forall]
  intro n
  rw [fib_mul_add_of_fib_eq_zero ha', fib_succ_pow_four_of_fib_eq_zero ha', one_mul]

theorem pisano_dvd_four_mul {m a : ℕ} (hm : m ≠ 0) (ha : m ∣ fib a) : pisano m ∣ 4 * a :=
  (isFibPeriod_iff_pisano_dvd hm).mp (isFibPeriod_four_mul ha)

/-- If `d ∣ m` (and `m ≠ 0`) then `π(d) ∣ π(m)`. -/
theorem pisano_dvd_pisano {d m : ℕ} (hm : m ≠ 0) (hdm : d ∣ m) : pisano d ∣ pisano m := by
  have hd : d ≠ 0 := by rintro rfl; exact hm (zero_dvd_iff.mp hdm)
  exact (isFibPeriod_iff_pisano_dvd hd).mp ((isFibPeriod_pisano hm).of_dvd hdm)

/-- Every period modulo `m > 2` is even. -/
theorem IsFibPeriod.even {m k : ℕ} (hm : 2 < m) (hk : IsFibPeriod m k) : Even k := by
  obtain ⟨h0, h1⟩ := hk
  have hsq := fib_succ_sq_of_fib_eq_zero h0
  rw [h1, one_pow] at hsq
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at hsq
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination hsq
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact absurd (Nat.le_of_dvd two_pos h2) (by omega)

/-- **Wall (1960)**: `π(m)` is even for `m > 2`. -/
theorem even_pisano {m : ℕ} (hm : 2 < m) : Even (pisano m) :=
  (isFibPeriod_pisano (by omega)).even hm

end WSS

namespace WSS

instance (m : ℕ) : DecidablePred (IsFibPeriod m) := fun k ↦ by
  unfold IsFibPeriod; infer_instance

/-- To compute `π(m)`: exhibit a positive period `k` and check no smaller positive period. -/
theorem pisano_eq_of {m k : ℕ} (hk : 0 < k) (h : IsFibPeriod m k)
    (hmin : ∀ j < k, 0 < j → ¬ IsFibPeriod m j) : pisano m = k := by
  apply le_antisymm (pisano_le hk h)
  by_contra hlt
  rw [not_le] at hlt
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 : (Nat.fib k : ℤ) = 0 := h.1
    rw [Nat.cast_eq_zero, Nat.fib_eq_zero] at h0
    omega
  exact hmin _ hlt (pisano_pos hm) (isFibPeriod_pisano hm)

end WSS
