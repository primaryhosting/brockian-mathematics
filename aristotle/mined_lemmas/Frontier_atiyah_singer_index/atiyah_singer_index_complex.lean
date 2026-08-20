/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is written as a plain block comment; its text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Atiyah–Singer index theorem states that for an elliptic (pseudo)differential operator
`D : Γ(E) → Γ(F)` on a closed manifold `M`, the *analytic index*

  `ind_a(D) = dim ker D - dim coker D`

equals the *topological index*, a quantity computed purely from the symbol data of `D`
(via characteristic classes).

Full pseudodifferential theory on manifolds is not available in Mathlib, so we formalize the

theorem atiyah_singer_index_complex (n : ℕ) (d : ∀ i, V i →ₗ[𝕜] V (i + 1))
    (hd : ∀ i, (d (i + 1)).comp (d i) = 0)
    (h0 : Subsingleton (V 0)) (hn : Subsingleton (V (n + 1))) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (cohomologyAt (d i) (d (i + 1)))
      = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (V (i + 1)) := by
  set a : ℕ → ℤ := fun i => (finrank 𝕜 (LinearMap.range (d i)) : ℤ) with ha
  have ha0 : a 0 = 0 := by
    have hd0 : LinearMap.range (d 0) = ⊥ := by
      rw [LinearMap.range_eq_bot]
      exact LinearMap.ext fun x => by simp [Subsingleton.elim x 0]
    simp [ha, hd0]
  have han : a n = 0 := by
    have : Subsingleton (LinearMap.range (d n)) := by
      constructor
      intro x y
      exact Subtype.ext (Subsingleton.elim _ _)
    simp [ha, finrank_zero_of_subsingleton]
  have key : ∀ i : ℕ,
      (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (cohomologyAt (d i) (d (i + 1)))
        - (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (V (i + 1))
        = (-1 : ℤ) ^ i * (a i + a (i + 1)) := by
    intro i
    have hc := finrank_cohomologyAt (d i) (d (i + 1)) (hd i)
    have hrk := LinearMap.finrank_range_add_finrank_ker (d (i + 1))
    have hV : (finrank 𝕜 (V (i + 1)) : ℤ)
        = (finrank 𝕜 (LinearMap.range (d (i + 1))) : ℤ)
          + (finrank 𝕜 (LinearMap.ker (d (i + 1))) : ℤ) := by exact_mod_cast hrk.symm
    rw [hc, hV, pow_succ]
    simp only [ha]
    ring
  have hsum : ∑ i ∈ Finset.range n,
      ((-1 : ℤ) ^ (i + 1) * finrank 𝕜 (cohomologyAt (d i) (d (i + 1)))
        - (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (V (i + 1)))
      = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (a i + a (i + 1)) :=
    Finset.sum_congr rfl fun i _ => key i
  rw [Finset.sum_sub_distrib, telescope a n, ha0, han] at hsum
  simp only [mul_zero, add_zero] at hsum
  omega

end Complex

end Frontier

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

