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


theorem exists_patch_length (hr : Computable r) (n : ℕ) :
    ∃ L, ∀ x, L ≤ x → acc M r (selfCode M hr) n x = acc M r (selfCode M hr) 0 x := by
  classical
  induction n with
  | zero => exact ⟨0, fun x _ => rfl⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih
    have main : ∀ L' : ℕ, (∀ x, L' ≤ x → ¬ (true ∈ cancelAt M r (selfCode M hr) n x)) →
        ∀ x, max L L' ≤ x → acc M r (selfCode M hr) (n+1) x = acc M r (selfCode M hr) 0 x := by
      intro L' hL' x hx
      have h1 : acc M r (selfCode M hr) (n+1) x = acc M r (selfCode M hr) n x := by
        refine acc_congr ?_
        intro i hi
        by_cases hin : i = n
        · subst hin
          have hfalse : false ∈ cancelAt M r (selfCode M hr) i x :=
            cancelAt_false_of_not_true M hr i x (hL' x (by omega))
          rw [contrib_eq_of_not_cancel hfalse, contrib_eq_of_not_cancel hfalse]
        · exact contrib_eq_contrib_of_iff (by omega)
      rw [h1, hL x (by omega)]
    by_cases hex : ∃ x0, true ∈ cancelAt M r (selfCode M hr) n x0
    · obtain ⟨x0, hx0⟩ := hex
      refine ⟨max L (x0+1), fun x hx => main (x0+1) (fun z hz hcz => ?_) x (by omega)⟩
      have := cancelAt_unique M hr hcz hx0
      omega
    · push_neg at hex
      exact ⟨max L 0, fun x hx => main 0 (fun z _ hcz => hex z hcz) x (by omega)⟩

/-- A patched level computes exactly the function `bigFun`. -/
