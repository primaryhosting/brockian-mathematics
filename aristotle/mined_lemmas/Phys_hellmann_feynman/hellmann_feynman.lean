import Mathlib
/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
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

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The map `λ ↦ H λ (ψ λ)` is differentiable, with the expected product rule, where the
operators `H λ` are `ℂ`-linear but the parameter `λ` is real. -/

theorem hellmann_feynman
    {H : ℝ → V →L[ℂ] V} {dH : V →L[ℂ] V} {psi : ℝ → V} {dpsi : V} {E : ℝ → ℝ} {t : ℝ}
    (hH : HasDerivAt H dH t)
    (hpsi : HasDerivAt psi dpsi t)
    (hnorm : ∀ l, inner ℂ (psi l) (psi l) = 1)
    (heig : ∀ l, H l (psi l) = (E l : ℂ) • psi l)
    (hsa : ∀ x y : V, inner ℂ (H t x) y = inner ℂ x (H t y)) :
    HasDerivAt E (inner ℂ (psi t) (dH (psi t))).re t := by
  -- The expectation value `⟪ψ λ, H λ (ψ λ)⟫` is exactly `E λ`.
  have hfun : (fun l => inner ℂ (psi l) (H l (psi l))) = fun l => ((E l : ℝ) : ℂ) := by
    funext l
    rw [heig l, inner_smul_right, hnorm l, mul_one]
  -- Differentiate the expectation value.
  have hHpsi : HasDerivAt (fun l => H l (psi l)) (dH (psi t) + H t dpsi) t :=
    hasDerivAt_apply_of_hasDerivAt hH hpsi
  have hf : HasDerivAt (fun l => inner ℂ (psi l) (H l (psi l)))
      (inner ℂ (psi t) (dH (psi t) + H t dpsi) + inner ℂ dpsi (H t (psi t))) t :=
    hpsi.inner ℂ hHpsi
  -- The terms involving `dψ` cancel.
  have horth : inner ℂ (psi t) dpsi + inner ℂ dpsi (psi t) = 0 :=
    inner_deriv_add_deriv_inner_eq_zero hpsi hnorm
  have e1 : inner ℂ (psi t) (H t dpsi) = (E t : ℂ) * inner ℂ (psi t) dpsi := by
    rw [← hsa, heig t, inner_smul_left, Complex.conj_ofReal]
  have e2 : inner ℂ dpsi (H t (psi t)) = (E t : ℂ) * inner ℂ dpsi (psi t) := by
    rw [heig t, inner_smul_right]
  have key : inner ℂ (psi t) (dH (psi t) + H t dpsi) + inner ℂ dpsi (H t (psi t))
      = inner ℂ (psi t) (dH (psi t)) := by
    rw [inner_add_right, e1, e2, add_assoc, ← mul_add, horth, mul_zero, add_zero]
  rw [hfun, key] at hf
  -- Take real parts.
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  simpa using hre

/-- Sanity check that the hypotheses of `Phys.hellmann_feynman` are satisfiable: for `H λ = λ · id`
on `ℂ`, the normalized eigenvector `ψ = 1` has eigenvalue `E λ = λ`, and indeed `dE/dλ = 1`. -/
example (t : ℝ) :
    HasDerivAt (fun l : ℝ => l) (inner ℂ (1 : ℂ) ((ContinuousLinearMap.id ℂ ℂ) (1 : ℂ))).re t := by
  refine hellmann_feynman (H := fun l => (l : ℂ) • ContinuousLinearMap.id ℂ ℂ)
    (psi := fun _ => (1 : ℂ)) (dpsi := 0) (E := fun l => l) ?_ (hasDerivAt_const t 1) ?_ ?_ ?_
  · have h : HasDerivAt (fun l : ℝ => ((l : ℝ) : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    simpa using h.smul_const (ContinuousLinearMap.id ℂ ℂ)
  · intro l; simp
  · intro l; simp
  · intro x y; simp [inner, mul_comm, mul_assoc]

end Phys

