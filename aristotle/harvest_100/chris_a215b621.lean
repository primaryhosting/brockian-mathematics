/-
/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header above is reproduced verbatim inside a comment block at the top of the file.)

import Mathlib

open scoped InnerProductSpace

namespace QPhys

/-- Applying a continuous `ℂ`-linear operator to a vector is a bounded `ℝ`-bilinear map.
(The Mathlib lemma `isBoundedBilinearMap_apply` only covers the case where the scalar field
of the operators coincides with the differentiability field; here we differentiate in `ℝ`
while the operators are `ℂ`-linear.) -/
theorem isBoundedBilinearMap_apply_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] :
    IsBoundedBilinearMap ℝ (fun p : (E →L[ℂ] E) × E => p.1 p.2) where
  add_left := by intros; simp
  smul_left := by intros; simp
  add_right := by intros; simp
  smul_right := by intros; simp
  bound := ⟨1, one_pos, by intro x y; simpa using x.le_opNorm y⟩

/-- Product rule for `s ↦ A s (u s)` where `A` is a curve of continuous `ℂ`-linear operators
and `u` a curve of vectors, both differentiated with respect to a real parameter. -/
theorem hasDerivAt_operator_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A : ℝ → (E →L[ℂ] E)} {dA : E →L[ℂ] E} {u : ℝ → E} {u' : E} {t : ℝ}
    (hA : HasDerivAt A dA t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => A s (u s)) (dA (u t) + A t u') t := by
  have h := (isBoundedBilinearMap_apply_real.hasFDerivAt (A t, u t)).comp_hasDerivAt t
    (hA.hasFDerivAt.prodMk hu.hasFDerivAt).hasDerivAt
  simpa [add_comm] using h

/-- **Ehrenfest's theorem.**

Let `E` be a complex inner product space (the space of states), `H : E →L[ℂ] E` a symmetric
(self-adjoint) Hamiltonian, `psi : ℝ → E` a time-dependent state obeying the Schrödinger
equation `i ℏ ψ'(t) = H ψ(t)`, and `A : ℝ → (E →L[ℂ] E)` a time-dependent observable with
time derivative `dA` at `t`. Then the expectation value `⟨A⟩(s) = ⟪ψ s, A s (ψ s)⟫` is
differentiable at `t` and

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`,

where `[H, A] = H ∘ A - A ∘ H` is the commutator. -/
theorem ehrenfest {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (hbar : ℝ) (hbar_ne : hbar ≠ 0)
    (H : E →L[ℂ] E) (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (psi : ℝ → E) (dpsi : E) (A : ℝ → (E →L[ℂ] E)) (dA : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi dpsi t) (hA : HasDerivAt A dA t)
    (hSchrodinger : (Complex.I * hbar) • dpsi = H (psi t)) :
    HasDerivAt (fun s => ⟪psi s, A s (psi s)⟫_ℂ)
      ((Complex.I / hbar) * ⟪psi t, (H.comp (A t) - (A t).comp H) (psi t)⟫_ℂ
        + ⟪psi t, dA (psi t)⟫_ℂ) t := by
  have hbarC : (hbar : ℂ) ≠ 0 := by exact_mod_cast hbar_ne
  -- Solve the Schrödinger equation for `ψ'(t)`.
  have hd : dpsi = (-Complex.I / hbar) • H (psi t) := by
    rw [← hSchrodinger, smul_smul,
      show (-Complex.I / hbar) * (Complex.I * hbar) = 1 by
        field_simp [Complex.I_sq],
      one_smul]
  -- The product rule for the expectation value.
  have hmain := hpsi.inner ℂ (hasDerivAt_operator_apply hA hpsi)
  convert hmain using 1
  rw [hd]
  simp only [map_smul, inner_smul_right, inner_smul_left, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right, map_div₀, map_neg, Complex.conj_I,
    Complex.conj_ofReal, inner_add_right]
  rw [hH (psi t) (A t (psi t))]
  field_simp
  ring

end QPhys

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

