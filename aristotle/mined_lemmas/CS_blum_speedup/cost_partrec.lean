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


theorem cost_partrec (M : BlumMeasure) : Partrec₂ M.cost := by
  have h : Partrec fun p : Code × ℕ => Nat.rfind (fun m => Part.some (M.graph p.1 p.2 m)) := by
    refine Partrec.rfind ?_
    exact (M.graph_computable).of_eq (fun p => rfl)
  refine (h.of_eq (fun p => ?_))
  apply Part.ext
  intro m
  rw [Nat.mem_rfind]
  simp only [Part.mem_some_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact (M.graph_spec _ _ _).mp h1.symm
  · intro hm
    refine ⟨((M.graph_spec _ _ _).mpr hm).symm, ?_⟩
    intro k hk
    by_cases hg : M.graph p.1 p.2 k = true
    · exact absurd (Part.mem_unique ((M.graph_spec _ _ _).mp hg) hm) (by omega)
    · simpa using hg

/-- The decidable test "the cost of `c` on `x` is at most `b`". -/
