import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma det_sub_smul (μ : ℂ) :
    (C12 - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)).det = ∏ k : ZMod 12, (lam k - μ) := by
  have hkey : (C12 - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)) * F
      = F * (Matrix.diagonal lam - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, C12_mul_F, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det hkey
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hdiag : Matrix.diagonal lam - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)
      = Matrix.diagonal fun k => lam k - μ := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  rw [hdiag, Matrix.det_diagonal] at hdet
  exact mul_right_cancel₀ F_det_ne_zero (hdet.trans (mul_comm _ _))

/-- **Hückel theory for the C₁₂ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₂` if and only if `μ = 2 cos(2πk/12)` for some
`k = 0, …, 11`. -/
