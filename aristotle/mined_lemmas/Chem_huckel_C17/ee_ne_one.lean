import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma ee_ne_one {m : ZMod 17} (hm : m ≠ 0) : ee m ≠ 1 := by
  intro h
  have hdvd : (17 : ℕ) ∣ m.val := (isPrimitiveRoot_zeta17.pow_eq_one_iff_dvd m.val).1 h
  have hlt : m.val < 17 := ZMod.val_lt m
  have hz : m.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  exact hm (by simpa [ZMod.val_eq_zero] using hz)

/-- Character sum: `∑_{k} ζ^{k m} = 17` if `m = 0`, and `0` otherwise. -/
