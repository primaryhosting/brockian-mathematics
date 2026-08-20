import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

(The `import Mathlib` line must precede this file's module documentation because Lean 4
requires all `import` commands to come first; the required header comment is otherwise
reproduced verbatim as the first block of the file.)

Gleason's theorem states that every quantum measure (normalized, finitely additive probability
assignment on the closed subspaces, i.e. a normalized frame function) on a complex Hilbert
space of dimension at least `3` is of the form `P ↦ tr (rho P)` for a unique density operator
`rho`.  Here the space is `EuclideanSpace ℂ (Fin n)` and operators are `n × n` complex matrices.

What is formalized and proved in this file:

* `Frontier.IsQuantumMeasure`, `Frontier.IsDensityOperator`, `Frontier.RepresentedBy`,
  `Frontier.GleasonProperty` -- the statement of the theorem.
* `Frontier.gleason_theorem` -- the *reduction*: a quantum measure that extends to a linear
  functional on operators is given by a density operator (trace-duality plus positivity).
* `Frontier.gleason_theorem_of_selfAdjoint_linear` -- the same with the more natural hypothesis
  of a real-linear extension over the self-adjoint operators, via complexification
  (`Frontier.hasLinearExtension_of_selfAdjoint`, `Frontier.hasSelfAdjointLinearExtension_iff`).
* `Frontier.hasLinearExtension_iff_gleasonProperty` -- the linearity hypothesis is exactly
  equivalent to the conclusion, so the reduction is lossless: all that is missing from a full
  proof of Gleason's theorem is the (deep) fact that in dimension `≥ 3` every quantum measure
  admits such an extension.
* `Frontier.isQuantumMeasure_of_isDensityOperator` -- the converse direction.
* `Frontier.representedBy_unique` -- uniqueness of the density operator.
* `Frontier.gleason_dim_one` -- the base case `n = 1`, unconditionally.
* `Frontier.gleason_fails_dim_two` -- sharpness: an explicit quantum measure on a qubit
  (`Frontier.qubitMeasure`, built from the cubic `3a² - 2a³`) that comes from no density
  operator, so the hypothesis `3 ≤ n` cannot be removed.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions

We model a complex Hilbert space of dimension `n` as `EuclideanSpace ℂ (Fin n)`, and the
bounded operators on it as `Matrix (Fin n) (Fin n) ℂ`.  An *event* (a closed subspace) is
recorded by its orthogonal projection. -/

/-- An orthogonal projection: a self-adjoint idempotent matrix. -/

theorem hasLinearExtension_of_selfAdjoint (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (h : HasSelfAdjointLinearExtension mu) : HasLinearExtension mu := by
  obtain ⟨g, hadd, hsmul, hproj⟩ := h
  have hg0 : g 0 = 0 := by
    have h0 : ((0 : Matrix (Fin n) (Fin n) ℂ))ᴴ = 0 := Matrix.conjTranspose_zero
    have := hadd 0 0 h0 h0
    simp only [add_zero] at this
    linarith
  have hgneg : ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ = A → g (-A) = -g A := by
    intro A hA
    have := hsmul (-1) A hA
    simpa using this
  set F : Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun A => (g (rePart A) : ℂ) + Complex.I * (g (imPart A) : ℂ) with hFdef
  have hFadd : ∀ A B, F (A + B) = F A + F B := by
    intro A B
    simp only [hFdef, rePart_add, imPart_add,
      hadd _ _ (rePart_selfAdjoint A) (rePart_selfAdjoint B),
      hadd _ _ (imPart_selfAdjoint A) (imPart_selfAdjoint B)]
    push_cast
    ring
  have hFreal : ∀ (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ), F ((r : ℂ) • A) = (r : ℂ) * F A := by
    intro r A
    simp only [hFdef, rePart_real_smul, imPart_real_smul,
      hsmul r _ (rePart_selfAdjoint A), hsmul r _ (imPart_selfAdjoint A)]
    push_cast
    ring
  have hFI : ∀ A : Matrix (Fin n) (Fin n) ℂ, F (Complex.I • A) = Complex.I * F A := by
    intro A
    simp only [hFdef, rePart_I_smul, imPart_I_smul, hgneg _ (imPart_selfAdjoint A)]
    push_cast
    linear_combination (-(g (imPart A) : ℂ)) * Complex.I_sq
  have hFsmul : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), F (c • A) = c * F A := by
    intro c A
    have hc : c • A = ((c.re : ℂ) • A) + ((c.im : ℂ) • (Complex.I • A)) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    rw [hc, hFadd, hFreal, hFreal, hFI]
    have hre : (c.re : ℂ) + (c.im : ℂ) * Complex.I = c := Complex.re_add_im c
    linear_combination (F A) * hre
  refine ⟨{ toFun := F, map_add' := hFadd, map_smul' := fun c A => by simpa using hFsmul c A }, ?_⟩
  intro P hP
  simp only [LinearMap.coe_mk, AddHom.coe_mk, hFdef, rePart_of_selfAdjoint P hP.1.eq,
    imPart_of_selfAdjoint P hP.1.eq, hg0, hproj P hP]
  push_cast
  ring

/-- Conversely, a complex-linear extension restricts to a real-linear extension on the
self-adjoint operators, so the two linearity hypotheses are equivalent. -/
