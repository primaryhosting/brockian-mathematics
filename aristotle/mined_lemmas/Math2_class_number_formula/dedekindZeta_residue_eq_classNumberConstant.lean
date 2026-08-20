/-
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
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

namespace Math2

open Filter NumberField NumberField.InfinitePlace NumberField.Units Topology

/-- The explicit constant appearing in the analytic class number formula:
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`, where `r₁`, `r₂` are the numbers of real and
complex places, `R_K` is the regulator, `h_K` the class number, `w_K` the number of roots of
unity and `d_K` the discriminant of `K`. -/

theorem dedekindZeta_residue_eq_classNumberConstant
    (K : Type*) [Field K] [NumberField K] :
    dedekindZeta_residue K = classNumberConstant K ∧ 0 < classNumberConstant K := by
  have h : dedekindZeta_residue K = classNumberConstant K := rfl
  exact ⟨h, h ▸ dedekindZeta_residue_pos K⟩

/-- **The analytic class number formula.**
For a number field `K`, the function `s ↦ (s - 1) * ζ_K(s)` tends, as `s → 1⁺` along the reals,
to the strictly positive constant
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`;
in other words, the Dedekind zeta function of `K` has a simple pole at `s = 1` whose residue is
given by this classical expression. -/
