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

private lemma compl_adj_of_mem_nonnbrs {v w : V} (h : w ∈ nonnbrs G v) : Gᶜ.Adj v w := by
  simp only [nonnbrs, Finset.mem_filter, Finset.mem_erase] at h
  exact ⟨fun hvw => h.1.1 hvw.symm, h.2⟩

