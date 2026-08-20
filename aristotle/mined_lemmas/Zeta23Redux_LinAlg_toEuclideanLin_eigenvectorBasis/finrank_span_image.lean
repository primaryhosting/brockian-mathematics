import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

lemma finrank_span_image
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (s : Finset (Fin d)) :
    Module.finrank ℂ (Submodule.span ℂ (b '' (s : Set (Fin d)))) = s.card := by
  have hli : LinearIndependent ℂ (fun i : (s : Finset (Fin d)) => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : (s : Finset (Fin d)) => b i) = b '' (s : Set (Fin d)) := by
    ext y; simp [Set.mem_image]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

/-- **Weyl monotonicity**: if all eigenvalues of the Hermitian perturbation `E` are bounded in
absolute value by `theta`, then the number of eigenvalues of `A + E` strictly above `theta` is at
most the number of strictly positive eigenvalues of `A`. -/
