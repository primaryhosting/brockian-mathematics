import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/

lemma sum_finSplit {M : Type*} [AddCommMonoid M] {r m : ℕ} (hr : r ≤ m) (g : Fin m → M) :
    ∑ j, g j =
      (∑ k : Fin r, g (Fin.castLE hr k)) + ∑ l : Fin (m - r), g (finSplit hr (Sum.inr l)) := by
  rw [← Equiv.sum_comp (finSplit hr) g, Fintype.sum_sum_type]
  simp only [finSplit_inl]

