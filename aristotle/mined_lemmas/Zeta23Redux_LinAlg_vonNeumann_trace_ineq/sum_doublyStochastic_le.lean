import Mathlib
/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/

lemma sum_doublyStochastic_le {a b mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    (pa pb : Equiv.Perm (Fin d)) (hma : mu = a ∘ pa) (hnb : nu = b ∘ pb)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, a i * b j * S i j ≤ ∑ i, mu i * nu i := by
  set c : ℝ := ∑ i, mu i * nu i with hc
  set f : Matrix (Fin d) (Fin d) ℝ → ℝ := fun M => ∑ i, ∑ j, a i * b j * M i j with hf
  have hlin : IsLinearMap ℝ f := by
    constructor
    · intro M N
      simp only [hf, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    · intro r M
      simp only [hf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hconv : Convex ℝ {M : Matrix (Fin d) (Fin d) ℝ | f M ≤ c} := convex_halfSpace_le hlin c
  have hsub : {x : Matrix (Fin d) (Fin d) ℝ | ∃ σ, Equiv.Perm.permMatrix ℝ σ = x} ⊆
      {M : Matrix (Fin d) (Fin d) ℝ | f M ≤ c} := by
    rintro _ ⟨σ, rfl⟩
    have hval : f (Equiv.Perm.permMatrix ℝ σ) = ∑ i, a i * b (σ i) := by
      simp [hf, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    show f _ ≤ c
    rw [hval]
    exact sum_perm_le hmu hnu pa pb hma hnb σ
  have h := convexHull_min hsub hconv
  rw [← doublyStochastic_eq_convexHull_permMatrix] at h
  exact h hS

/-- `z * star z` is the squared norm of `z`. -/
