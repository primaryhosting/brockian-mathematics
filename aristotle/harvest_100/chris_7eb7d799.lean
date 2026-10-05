import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a family of (symmetric at the point of interest) operators on a
complex inner product space, depending on a real parameter `l`, and suppose that for every `l`
the vector `ψ l` is a normalized eigenvector of `H l` with real eigenvalue `En l`.
If `H`, `ψ` and `En` are differentiable at `lam`, then

  `dEn/dl = ⟪ψ, (dH/dl) ψ⟫`  at `l = lam`. -/
theorem hellmann_feynman
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    {H : ℝ → (E →L[ℂ] E)} {ψ : ℝ → E} {En : ℝ → ℝ}
    {lam : ℝ} {H' : E →L[ℂ] E} {ψ' : E} {En' : ℝ}
    (hH : HasDerivAt H H' lam) (hψ : HasDerivAt ψ ψ' lam) (hE : HasDerivAt En En' lam)
    (hnorm : ∀ l, ⟪ψ l, ψ l⟫_ℂ = 1)
    (heig : ∀ l, H l (ψ l) = (En l : ℂ) • ψ l)
    (hsymm : ∀ x y : E, ⟪H lam x, y⟫_ℂ = ⟪x, H lam y⟫_ℂ) :
    (En' : ℂ) = ⟪ψ lam, H' (ψ lam)⟫_ℂ := by
  set p := ψ lam with hp
  -- Differentiating the normalization condition.
  have hnorm0 : ⟪p, ψ'⟫_ℂ + ⟪ψ', p⟫_ℂ = 0 := by
    have h1 : HasDerivAt (fun l => ⟪ψ l, ψ l⟫_ℂ) (⟪p, ψ'⟫_ℂ + ⟪ψ', p⟫_ℂ) lam := hψ.inner ℂ hψ
    have h2 : HasDerivAt (fun l => ⟪ψ l, ψ l⟫_ℂ) 0 lam := by
      have : (fun l => ⟪ψ l, ψ l⟫_ℂ) = fun _ => (1 : ℂ) := funext hnorm
      rw [this]
      exact hasDerivAt_const _ _
    exact h1.unique h2
  -- Differentiating the operator applied to the state.
  have hHR : HasDerivAt (fun l => (H l).restrictScalars ℝ) (H'.restrictScalars ℝ) lam := by
    exact (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt lam hH
  have hHψ : HasDerivAt (fun l => H l (ψ l)) (H' p + H lam ψ') lam := by
    simpa using hHR.clm_apply hψ
  -- Differentiating the expectation value.
  have hf : HasDerivAt (fun l => ⟪ψ l, H l (ψ l)⟫_ℂ)
      (⟪p, H' p + H lam ψ'⟫_ℂ + ⟪ψ', H lam p⟫_ℂ) lam := hψ.inner ℂ hHψ
  have hexp : (fun l => ⟪ψ l, H l (ψ l)⟫_ℂ) = fun l => ((En l : ℂ)) := by
    funext l
    rw [heig l, inner_smul_right, hnorm l, mul_one]
  have hg : HasDerivAt (fun l => ((En l : ℂ))) (En' : ℂ) lam := hE.ofReal_comp
  rw [hexp] at hf
  have key : (En' : ℂ) = ⟪p, H' p + H lam ψ'⟫_ℂ + ⟪ψ', H lam p⟫_ℂ := hg.unique hf
  -- Simplify using symmetry and the eigenvalue equation.
  have e1 : ⟪p, H lam ψ'⟫_ℂ = (En lam : ℂ) * ⟪p, ψ'⟫_ℂ := by
    rw [← hsymm p ψ', hp, heig lam, inner_smul_left, Complex.conj_ofReal]
  have e2 : ⟪ψ', H lam p⟫_ℂ = (En lam : ℂ) * ⟪ψ', p⟫_ℂ := by
    rw [hp, heig lam, inner_smul_right]
  rw [inner_add_right, e1, e2] at key
  have : (En lam : ℂ) * ⟪p, ψ'⟫_ℂ + (En lam : ℂ) * ⟪ψ', p⟫_ℂ = 0 := by
    rw [← mul_add, hnorm0, mul_zero]
  linear_combination key + this

/-- Sanity check: the hypotheses of `Phys.hellmann_feynman` are satisfiable.
Take `E = ℂ`, `H l = l • id`, `ψ l = 1`, `En l = l`; then `dEn/dl = 1 = ⟪ψ, (dH/dl) ψ⟫`. -/
example :
    ∃ (H : ℝ → (ℂ →L[ℂ] ℂ)) (ψ : ℝ → ℂ) (En : ℝ → ℝ) (H' : ℂ →L[ℂ] ℂ) (ψ' : ℂ) (En' : ℝ),
      HasDerivAt H H' 0 ∧ HasDerivAt ψ ψ' 0 ∧ HasDerivAt En En' 0 ∧
      (∀ l, ⟪ψ l, ψ l⟫_ℂ = 1) ∧ (∀ l, H l (ψ l) = (En l : ℂ) • ψ l) ∧
      (∀ x y : ℂ, ⟪H 0 x, y⟫_ℂ = ⟪x, H 0 y⟫_ℂ) ∧ En' ≠ 0 := by
  refine ⟨fun l => (l : ℂ) • ContinuousLinearMap.id ℂ ℂ, fun _ => 1, fun l => l,
    ContinuousLinearMap.id ℂ ℂ, 0, 1, ?_, hasDerivAt_const _ _, hasDerivAt_id _, ?_, ?_, ?_,
    one_ne_zero⟩
  · simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).smul_const (ContinuousLinearMap.id ℂ ℂ)
  · intro l; simp
  · intro l; simp
  · intro x y; simp [mul_comm]

end Phys

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

