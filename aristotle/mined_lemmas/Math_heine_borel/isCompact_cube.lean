/-
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The closed cube `[-r, r]^n` in `ℝ^n` is compact.  This is the finite-product
(Tychonoff) consequence of the compactness of a closed interval in `ℝ`, transported
along the homeomorphism between the Euclidean space `ℝ^n` and the product space
`Fin n → ℝ`. -/

theorem isCompact_cube (n : ℕ) (r : ℝ) :
    IsCompact {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Set.Icc (-r) r} := by
  set e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph with he
  have hea : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), e x i = x i := fun x i =>
    PiLp.continuousLinearEquiv_apply 2 ℝ _ x i
  have hK : IsCompact (Set.univ.pi (fun _ : Fin n => Set.Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have h2 : IsCompact (e ⁻¹' (Set.univ.pi (fun _ : Fin n => Set.Icc (-r) r))) :=
    e.isCompact_preimage.mpr hK
  convert h2 using 1
  ext x
  constructor
  · intro hx i _
    rw [hea]
    exact hx i
  · intro hx i
    have hxi := hx i (Set.mem_univ i)
    rw [hea] at hxi
    exact hxi

/-- **Heine–Borel theorem**: a subset of `ℝ^n` is compact if and only if it is
closed and bounded. -/
