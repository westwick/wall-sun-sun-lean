import WSS.Examples

/-!
# Wall's question and the Sun–Sun theorem

* `wallQuestion_iff_noWallSunSunPrimes` (**proved**): Wall's 1960 question "is
  `π(p²) ≠ π(p)` for every prime `p`?" has answer *yes* exactly when there are no Wall–Sun–Sun
  primes. (The primes 2 and 5, excluded from the WSS definition, are checked directly:
  `π(4) = 6 ≠ 3 = π(2)` and `π(25) = 100 ≠ 20 = π(5)`.)
* `SunSunStatement` (**stated only, not proved**): Sun & Sun (1992), Acta Arith. 60: a
  counterexample to the first case of Fermat's Last Theorem for exponent `p` forces `p` to be
  a Wall–Sun–Sun prime. This is recorded as a `Prop` (not an axiom), so nothing depends on it.
  Formalizing it would need the Kummer/Wieferich-type machinery behind the original proof.
-/

namespace WSS

open Nat

/-- Wall's question (1960): is `π(p²) ≠ π(p)` for every prime `p`? (Open.) -/
def WallQuestion : Prop := ∀ p : ℕ, p.Prime → pisano (p ^ 2) ≠ pisano p

/-- There are no Wall–Sun–Sun primes. (Open; heuristically false.) -/
def NoWallSunSunPrimes : Prop := ∀ p : ℕ, ¬ IsWallSunSunPrime p

theorem pisano_four : pisano 4 = 6 := pisano_eq_of (by norm_num) (by decide) (by decide)
theorem pisano_two : pisano 2 = 3 := pisano_eq_of (by norm_num) (by decide) (by decide)
theorem pisano_five : pisano 5 = 20 := pisano_eq_of (by norm_num) (by decide) (by decide)
theorem pisano_twentyfive : pisano 25 = 100 :=
  pisano_eq_of (by norm_num) (by decide) (by decide)

/-- **Wall's question is equivalent to the non-existence of Wall–Sun–Sun primes.** -/
theorem wallQuestion_iff_noWallSunSunPrimes : WallQuestion ↔ NoWallSunSunPrimes := by
  constructor
  · intro hW p hwss
    obtain ⟨hp, hp2, hp5, -⟩ := id hwss
    have : Fact p.Prime := ⟨hp⟩
    exact hW p hp ((isWallSunSunPrime_iff_pisano hp2 hp5).mp hwss)
  · intro hN p hp
    by_cases hp2 : p = 2
    · subst hp2; rw [show (2 : ℕ) ^ 2 = 4 by norm_num, pisano_four, pisano_two]; norm_num
    by_cases hp5 : p = 5
    · subst hp5; rw [show (5 : ℕ) ^ 2 = 25 by norm_num, pisano_twentyfive, pisano_five]; norm_num
    have : Fact p.Prime := ⟨hp⟩
    exact fun h ↦ hN p ((isWallSunSunPrime_iff_pisano hp2 hp5).mpr h)

/-- A counterexample to the first case of Fermat's Last Theorem for the exponent `p`. -/
def FLTFirstCaseCounterexample (p : ℕ) : Prop :=
  ∃ x y z : ℤ, ¬ (p : ℤ) ∣ x * y * z ∧ x ^ p + y ^ p = z ^ p

/-- **Sun & Sun (1992)** — STATED ONLY, NOT PROVED HERE. -/
def SunSunStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → FLTFirstCaseCounterexample p → IsWallSunSunPrime p

end WSS
