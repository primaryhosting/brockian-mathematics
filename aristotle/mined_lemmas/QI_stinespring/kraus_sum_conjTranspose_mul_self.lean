import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder MatrixOrder

namespace QI

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The partial trace over the second (environment) tensor factor. -/

theorem kraus_sum_conjTranspose_mul_self {ι : Type} [Fintype ι] (K : ι → Matrix B A ℂ)
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (htp : IsTracePreserving Φ)
    (hK : ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ μ, K μ * ρ * (K μ)ᴴ) :
    ∑ μ, (K μ)ᴴ * K μ = 1 := by
  have key : ∀ ρ : Matrix A A ℂ, ((∑ μ, (K μ)ᴴ * K μ) * ρ).trace = ρ.trace := by
    intro ρ
    have h := htp ρ
    rw [hK ρ] at h
    rw [Finset.sum_mul, Matrix.trace_sum]
    rw [Matrix.trace_sum] at h
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  ext a a'
  have h := key (Matrix.single a' a 1)
  rw [trace_mul_single, trace_single_one] at h
  rw [h, Matrix.one_apply]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- Any finite family of matrices can be re-indexed by `Fin (k+1)`, padding with zeros. -/
