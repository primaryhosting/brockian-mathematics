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


theorem stepGraph_spec (c : Code) (x m : ℕ) : stepGraph c x m = true ↔ m ∈ stepCost c x := by
  simp only [stepGraph, decide_eq_true_eq, stepCost, Part.mem_mk_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨m, h1⟩, ?_⟩
    refine (Nat.find_eq_iff _).mpr ⟨h1, ?_⟩
    intro n hn hns
    rcases h2 with h2 | h2
    · omega
    · exact absurd (isSome_evaln_mono (by omega : n ≤ m - 1) hns) (by simp [h2])
  · rintro ⟨h, hf⟩
    subst hf
    refine ⟨Nat.find_spec h, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
    · exact Or.inl h0
    · right
      have := Nat.find_min h (m := Nat.find h - 1) (by omega)
      simpa using this

