import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

theorem schmidt_decomposition_tensor {m n : ℕ}
    (psi : EuclideanSpace ℂ (Fin m) ⊗[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)),
      (∀ i, 0 < s i) ∧ Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      psi = ∑ i, (s i : ℂ) • (u i ⊗ₜ[ℂ] v i) ∧
      (∀ (r' : ℕ) (s' : Fin r' → ℝ) (u' : Fin r' → EuclideanSpace ℂ (Fin m))
        (v' : Fin r' → EuclideanSpace ℂ (Fin n)), (∀ i, 0 < s' i) → Orthonormal ℂ u' →
        Orthonormal ℂ v' → psi = ∑ i, (s' i : ℂ) • (u' i ⊗ₜ[ℂ] v' i) →
        Multiset.map s' Finset.univ.val = Multiset.map s Finset.univ.val) := by
  obtain ⟨r, s, u, v, hd⟩ := schmidt_exists (tensorEquiv m n psi)
  refine ⟨r, s, u, v, hd.pos, hd.left_orthonormal, hd.right_orthonormal, ?_, ?_⟩
  · refine (tensorEquiv m n).injective ?_
    ext p
    rw [tensorEquiv_apply_of_sum]
    exact hd.amp p.1 p.2
  · intro r' s' u' v' hpos' hu' hv' heq
    refine schmidt_coefficients_unique ⟨hpos', hu', hv', ?_⟩ hd
    intro j k
    conv_lhs => rw [heq]
    exact tensorEquiv_apply_of_sum s' u' v' j k

end QI

