import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

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

namespace Math2

/-- The standard symplectic vector space `ℝ^{2(n+1)}`, realized as the Euclidean space with
index set `Fin (n+1) × Fin 2`: the index `(i, 0)` is the position coordinate `q i` and the
index `(i, 1)` is the momentum coordinate `p i`. -/
abbrev SympSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) × Fin 2)

/-- The standard symplectic form `ω = ∑ i, dq i ∧ dp i` on `SympSpace n`. -/

lemma omegaForm_smul_right {n : ℕ} (c : ℝ) (x y : SympSpace n) :
    omegaForm x (c • y) = c * omegaForm x y := by
  simp only [omegaForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

