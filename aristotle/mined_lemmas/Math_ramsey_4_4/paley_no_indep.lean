/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem paley_no_indep (s : Finset (Fin 17)) : ¬ paley17ᶜ.IsNClique 4 s := by
  intro h
  obtain ⟨a, b, c, d, hab, hbc, hcd, rfl⟩ := card_eq_four_sorted h.2
  have hcl := h.1
  refine paley_indep_check a b c d hab hbc hcd ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [← Bool.not_eq_true]
      exact (hcl (by simp) (by simp) (by order)).2

