/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/

lemma paleyNonAdj_of_compl_adj {a b : Fin 17} (h : paley17ᶜ.Adj a b) : paleyNonAdj a b := by
  obtain ⟨hne, hadj⟩ := h
  simp only [paleyNonAdj, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  refine ⟨hne, ?_⟩
  simpa [paley17] using hadj

