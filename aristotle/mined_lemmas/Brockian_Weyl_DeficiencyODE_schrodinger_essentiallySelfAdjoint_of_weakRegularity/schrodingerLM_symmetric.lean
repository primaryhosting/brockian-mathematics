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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter

namespace Brockian.Weyl.DeficiencyODE

/-!
## Abstract deficiency criterion

An unbounded operator is presented here as a linear map `T` on a complex Hilbert space `H`
together with a distinguished (dense) *domain* `D`; the operator of interest is the
restriction `T|_D`.  Essential self-adjointness of a densely defined symmetric operator is
equivalent to the vanishing of both deficiency spaces `ker (T* ∓ i)`, i.e. to the density of
the ranges of `T ± i`; this is the definition used below.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T` is symmetric on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫` for `x, y ∈ D`. -/

lemma schrodingerLM_symmetric (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) (φ ψ : L2Z) :
    ⟪schrodingerLM V hV φ, ψ⟫_ℂ = ⟪φ, schrodingerLM V hV ψ⟫_ℂ := by
  show ⟪shiftLM 1 φ + shiftLM (-1) φ + potentialLM V hV φ, ψ⟫_ℂ
      = ⟪φ, shiftLM 1 ψ + shiftLM (-1) ψ + potentialLM V hV ψ⟫_ℂ
  rw [inner_add_left, inner_add_left, inner_add_right, inner_add_right,
    inner_shiftLM_left 1, inner_shiftLM_left (-1), inner_potentialLM_left]
  simp only [neg_neg]
  ring

/-- **Essential self-adjointness of the Schrödinger operator under weak regularity of the
potential.**

The potential `V` is assumed only to be real valued and bounded; no continuity, smoothness or
any other regularity is required (weak regularity).  The Schrödinger operator
`(Hψ) n = ψ (n+1) + ψ (n-1) + V n * ψ n` on `ℓ²(ℤ)`, defined on the domain `finSupp` of
finitely supported sequences, is then symmetric and essentially self-adjoint: both deficiency
spaces vanish, i.e. the ranges of `H ± i` on the domain are dense.  This is the unconditional
form of the statement: no essential self-adjointness (limit-point) hypothesis is assumed. -/
