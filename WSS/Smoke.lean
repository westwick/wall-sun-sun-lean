import Mathlib

/-! Toolchain smoke test: Mathlib loads, `Nat.fib` and Legendre symbols are usable,
and small facts check by `decide`/`norm_num`. Not part of the research results. -/

namespace WSS.Smoke

/-- F(6) = 8, and 7 ∣ F(8) (here (7/5) = -1, so the index is p + 1 = 8). -/
example : Nat.fib 6 = 8 := by decide
example : 7 ∣ Nat.fib 8 := by decide

/-- 7² does not divide F(8) = 21, so 7 is not a Wall-Sun-Sun prime. -/
example : ¬ (7 ^ 2 ∣ Nat.fib 8) := by decide

/-- Mathlib's Fibonacci addition formula is available. -/
example (m n : ℕ) :
    Nat.fib (m + n + 1) = Nat.fib m * Nat.fib n + Nat.fib (m + 1) * Nat.fib (n + 1) :=
  Nat.fib_add m n

end WSS.Smoke
