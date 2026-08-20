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


theorem cost_gt_of_not_elig {i y : ℕ} (h : false ∈ elig M r C i y) {c : ℕ}
    (hc : c ∈ M.cost (ofNat Code i) y) : ∃ K ∈ maxK M C (i+1) y, r K < c := by
  obtain ⟨K, hK, hcl⟩ := elig_mem_iff.mp h
  refine ⟨K, hK, ?_⟩
  by_contra hcon
  have hct : costLe M (ofNat Code i) y (r K) = true :=
    (costLe_iff M (ofNat Code i) y (r K)).mpr ⟨c, by omega, hc⟩
  rw [← hcl] at hct
  exact Bool.false_ne_true hct

