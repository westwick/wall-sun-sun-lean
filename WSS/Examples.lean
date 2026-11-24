import WSS.Wall

/-! Small sanity checks of the definitions (kernel-checked by `decide`/`norm_num`;
no `native_decide`). Cross-checked against an independent Python computation in
`lean/scripts/check_definitions.py`. -/

namespace WSS

open Nat

example : legendreSym 5 7 = -1 := by norm_num
example : legendreSym 5 11 = 1 := by norm_num
example : wallIndex 7 = 8 := by norm_num [wallIndex]
example : wallIndex 11 = 10 := by norm_num [wallIndex]

/-- Classical small Pisano periods. -/
example : pisano 2 = 3 := pisano_eq_of (by norm_num) (by decide) (by decide)
example : pisano 5 = 20 := pisano_eq_of (by norm_num) (by decide) (by decide)
example : pisano 7 = 16 := pisano_eq_of (by norm_num) (by decide) (by decide)
example : pisano 10 = 60 := pisano_eq_of (by norm_num) (by decide) (by decide)
example : pisano 11 = 10 := pisano_eq_of (by norm_num) (by decide) (by decide)

/-- 7 is not a Wall–Sun–Sun prime: `F(8) = 21` is not divisible by 49. -/
theorem not_isWallSunSunPrime_seven : ¬ IsWallSunSunPrime 7 := by
  rintro ⟨-, -, -, h⟩
  rw [show wallIndex 7 = 8 by norm_num [wallIndex]] at h
  revert h; decide

/-- Hence, by Wall's theorem, `π(49) = 7 π(7) = 112`. -/
example : pisano 49 = 112 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  change pisano (7 ^ 2) = 112
  rw [(not_isWallSunSunPrime_iff (p := 7) (by norm_num) (by norm_num)).mp
    not_isWallSunSunPrime_seven]
  rw [pisano_eq_of (m := 7) (k := 16) (by norm_num) (by decide) (by decide)]

end WSS
