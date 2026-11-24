-- Run: cd lean && lake env lean scripts/Axioms.lean
-- Expected: every theorem depends only on [propext, Classical.choice, Quot.sound].
import WSS
open WSS
#print axioms wall_equivalence
#print axioms isWallSunSunPrime_iff_pisano
#print axioms isWallSunSunPrime_iff_fibQuotient
#print axioms not_isWallSunSunPrime_iff
#print axioms pisano_sq_eq_or
#print axioms prime_dvd_fib_wallIndex
#print axioms pisano_prime_dvd
#print axioms even_pisano
#print axioms isFibPeriod_iff_pisano_dvd
#print axioms wallIndex_eq
#print axioms wallQuestion_iff_noWallSunSunPrimes
#print axioms legendreSym_five_eq_one_iff
#print axioms pisano_sq_dvd
#print axioms isFibPeriod_sq_of
#print axioms sq_dvd_fib_mul
#print axioms fib_prime_zmod
#print axioms two_mul_fib_prime_sub_one_zmod
#print axioms exists_isFibPeriod
