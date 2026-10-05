/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped InnerProductSpace

namespace Phys

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Setup

Throughout, `H s` is a time–dependent (self-adjoint) Hamiltonian, `Ev s` a real eigenvalue,
and `P s` the orthogonal projection onto the corresponding eigenspace.  `P₁`, `P₂` are the
first and second derivatives of `P`, `H'` the derivative of `H` and `Ev'` the derivative of `Ev`.
-/

section Defs

variable (H H' P P₁ : ℝ → (E →L[ℂ] E)) (Ev Ev' : ℝ → ℝ)

/-- The shifted Hamiltonian `H s - Ev s` with the eigenprojection added, so that it becomes
invertible exactly when `Ev s` is an isolated (gapped) eigenvalue. -/

lemma norm_psi_const (hHsa : ∀ s, IsSelfAdjoint (H s)) {T : ℝ} {ψ : ℝ → E}
    (hψ : ∀ s, HasDerivAt ψ ((-(Complex.I * (T : ℂ))) • (H s) (ψ s)) s) (s : ℝ) :
    ‖ψ s‖ = ‖ψ 0‖ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun r => ⟪ψ r, ψ r⟫_ℂ) 0 t := by
    intro t
    have h := hasDerivAt_inner_apply hHsa hψ (A := fun _ => (1 : E →L[ℂ] E)) (A' := fun _ => 0)
      (s := t) (hasDerivAt_const t _)
    simpa using h
  have h2 := is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := fun r => ⟪ψ r, ψ r⟫_ℂ)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s 0
  simp only [inner_self_eq_norm_sq_to_K] at h2
  have h3 : (‖ψ s‖ : ℝ) ^ 2 = (‖ψ 0‖ : ℝ) ^ 2 := by exact_mod_cast h2
  nlinarith [norm_nonneg (ψ s), norm_nonneg (ψ 0)]

/-! ## The adiabatic theorem -/

/--
**Adiabatic theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a `C¹` family of self-adjoint operators on a complex Hilbert
space `E`, let `Ev : ℝ → ℝ` be a `C¹` family of eigenvalues and `P : ℝ → (E →L[ℂ] E)` a `C²`
family of orthogonal projections onto the corresponding eigenspaces (`H s * P s = Ev s • P s`).
Assume the eigenvalue is *nondegenerate* (each `P s` is a rank-one projection onto a unit
vector) and *gapped*, encoded by the invertibility of `H s - Ev s + P s`.

Then there is a constant `C` such that for every adiabatic parameter `T ≥ 1` and every
solution `ψ` of the Schrödinger equation `ψ' = -i T H(s) ψ` starting in the eigenspace at
time `0`, the state stays in the instantaneous eigenspace up to an error `O(1/T)`:
`‖ψ s - P s (ψ s)‖² ≤ C / T` for all `s ∈ [0,1]`.

The nondegeneracy hypothesis `hrank` is stated because it is part of the physical statement;
the proof in fact works for the spectral projection of any isolated eigenvalue.
-/
