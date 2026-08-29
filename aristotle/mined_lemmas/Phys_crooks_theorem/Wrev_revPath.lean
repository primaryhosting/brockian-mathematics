/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

lemma Wrev_revPath (γ : Fin (N + 1) → X) : Wrev E N (revPath γ) = -Wfwd E N γ := by
  simp only [Wrev, Wfwd, Erev, st_revPath, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have e1 : N - (N - 1 - s + 1) = s := by omega
  have e2 : N - (N - 1 - s) = s + 1 := by omega
  rw [e1, e2]
  ring

