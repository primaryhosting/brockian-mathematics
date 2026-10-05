/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem C7adj_mulVec_fourierVec (k : ℕ) :
    C7adj.mulVec (fourierVec k) = (zeta ^ k + (zeta ^ k)⁻¹) • fourierVec k := by
  have h7 : (7 : ZMod 7) = 0 := by decide
  have hinv : (zeta ^ k)⁻¹ = zeta ^ (k * 6) := by
    have hmul : zeta ^ k * zeta ^ (k * 6) = 1 := by
      rw [← pow_add, show k + k * 6 = 7 * k by ring, pow_mul, zeta_pow_seven, one_pow]
    exact inv_eq_of_mul_eq_one_right hmul
  funext i
  rw [C7adj_mulVec]
  have hsub : i - 1 = i + 6 := by linear_combination -h7
  rw [hsub, fourierVec_add, fourierVec_add]
  have h1 : fourierVec k 1 = zeta ^ k := by
    rw [fourierVec, show ((1 : ZMod 7)).val = 1 from rfl, mul_one]
  have h6 : fourierVec k 6 = zeta ^ (k * 6) := by
    rw [fourierVec, show ((6 : ZMod 7)).val = 6 from rfl]
  rw [h1, h6, hinv, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The characteristic polynomial identities -/

