import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open scoped Classical

namespace Math2

variable {n : ℕ}

/-- A subset of `𝔽₃ⁿ` is a *cap set* if it contains no line, i.e. no three points summing to
zero other than the degenerate ones `x + x + x = 0`.  Equivalently (see
`Math2.threeAPFree_of_isCapSet`) it contains no nontrivial three-term arithmetic progression. -/

lemma exists_capSetNumber (n : ℕ) :
    ∃ A : Finset (Fin n → ZMod 3), IsCapSet A ∧ capSetNumber n = #A := by
  have hne : ((univ : Finset (Finset (Fin n → ZMod 3))).filter
      (fun A => IsCapSet A)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [IsCapSet]
  obtain ⟨A, hA, hAeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨A, (Finset.mem_filter.1 hA).2, hAeq⟩

/-- **The cap set theorem**, asymptotic form: the maximal size of a cap set in `𝔽₃ⁿ` is
`o(3ⁿ)`. -/
