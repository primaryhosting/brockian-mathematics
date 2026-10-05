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

/-! ## Setup: the standard symplectic vector space -/

/-- The standard symplectic phase space `ℝ^{2n}`, with coordinates indexed by `ι ⊕ ι`:
`Sum.inl i` is the `i`-th position coordinate `qᵢ`, and `Sum.inr i` the `i`-th momentum
coordinate `pᵢ`.  It carries the standard Euclidean inner product. -/
abbrev Phase (ι : Type*) [Fintype ι] := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (qᵢ(x) pᵢ(y) - pᵢ(x) qᵢ(y))`. -/

lemma inner_proj_right (u v : E) (hu : u ≠ 0) :
    ⟪v, v - (⟪u, v⟫ / ‖u‖ ^ 2) • u⟫ = ‖v - (⟪u, v⟫ / ‖u‖ ^ 2) • u‖ ^ 2 := by
  have h : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_proj_sq,
    real_inner_comm v u]
  field_simp
  ring

