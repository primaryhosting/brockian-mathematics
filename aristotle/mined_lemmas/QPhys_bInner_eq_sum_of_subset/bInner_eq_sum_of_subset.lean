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
# A model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are not vacuous:
we build an explicit complex inner product space (the polynomials `ℂ[X]` with the
Bargmann–Fock inner product `⟪p, q⟫ = ∑ n ! * conj (pₙ) * qₙ`), two symmetric operators
`Xop`, `Pop` on it satisfying `[Xop, Pop] = 2 i`, and a normalized state.
-/

import Mathlib
import RequestProject.HeisenbergUncertainty

/-!
# A model for the canonical commutation relation (Bargmann–Fock space of polynomials)
-/

namespace QPhys

open Polynomial ComplexConjugate

/-- The Bargmann–Fock inner product on polynomials: `⟪p, q⟫ = ∑ₙ n! * conj pₙ * qₙ`. -/

lemma bInner_eq_sum_of_subset {p : ℂ[X]} {s : Finset ℕ} (hs : p.support ⊆ s) (q : ℂ[X]) :
    bInner p q = ∑ n ∈ s, (Nat.factorial n : ℂ) * conj (p.coeff n) * q.coeff n := by
  refine Finset.sum_subset hs fun n _ hn => ?_
  have : p.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
  simp [this]

