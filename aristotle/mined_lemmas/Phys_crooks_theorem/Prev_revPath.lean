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

lemma Prev_revPath (γ : Fin (N + 1) → X) :
    Prev β E p N (revPath γ) =
      Real.exp (-β * E N (st γ N)) / Zpf β E N *
        ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) := by
  have hprod : (∏ s ∈ range N, prev p N s (st (revPath γ) s) (st (revPath γ) (s + 1))) =
      ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) := by
    simp only [prev, st_revPath]
    rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    have e1 : N - 1 - (N - 1 - t) = t := by omega
    have e2 : N - (N - 1 - t) = t + 1 := by omega
    have e3 : N - (N - 1 - t + 1) = t := by omega
    rw [e1, e2, e3]
  have hZ : Zpf β (Erev E N) 0 = Zpf β E N := by
    simp [Zpf, Erev]
  rw [Prev, hprod, hZ]
  simp [Erev, st_revPath]

omit [Fintype X] in
/-- The core exponential identity behind the Crooks relation. -/
