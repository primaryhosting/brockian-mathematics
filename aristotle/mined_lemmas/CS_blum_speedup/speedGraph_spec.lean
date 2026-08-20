/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/


theorem speedGraph_spec (e : Code) (x m : ℕ) :
    speedGraph r e x m = true ↔ m ∈ speedCost r e x := by
  unfold speedGraph speedCost
  by_cases h : padIdx e x ≤ x
  · rw [if_pos h]
    simp only [(padLe_iff e x).mpr h, cond_true, decide_eq_true_eq, Part.mem_some_iff]
  · rw [if_neg h]
    have hpl : padLe e x = false := by
      simpa using fun hc => h ((padLe_iff e x).mp hc)
    simp only [hpl, cond_false, Bool.and_eq_true, decide_eq_true_eq, Part.mem_map_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨m - bigB r x, (stepGraph_spec _ _ _).mp h2, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨by omega, ?_⟩
      have hsub : a + bigB r x - bigB r x = a := by omega
      rw [hsub]
      exact (stepGraph_spec _ _ _).mpr ha

