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


theorem acc_dom_self (hr : Computable r) : ∀ x n, (acc M r (selfCode M hr) n x).Dom := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x IH =>
    have key : ∀ d n, x + 1 ≤ n + d → (acc M r (selfCode M hr) n x).Dom := by
      intro d
      induction d with
      | zero =>
        intro n hn
        refine acc_dom_of ?_
        intro i hi
        rw [contrib_of_lt (by omega)]
        trivial
      | succ d ihd =>
        intro n hn
        refine acc_dom_of ?_
        intro i hi
        by_cases hni : n ≤ i
        · have helig : ∀ y ≤ x, (elig M r (selfCode M hr) i y).Dom := by
            intro y hy
            refine elig_dom_of (maxK_dom _ _ ?_)
            intro L hL
            refine (M.dom_eq _ _).mpr ?_
            rw [eval_patch_self M hr (i+1) L y hL]
            rcases Nat.lt_or_ge y x with hyx | hyx
            · exact IH y hyx (i+1)
            · have hyx' : y = x := by omega
              subst hyx'
              exact ihd (i+1) (by omega)
          have hc : (cancelAt M r (selfCode M hr) i x).Dom :=
            cancelAt_dom_of (helig x le_rfl) (noElig_dom_of (fun y _ hy => helig y (by omega)))
          refine contrib_dom_of hc ?_
          intro hct
          exact (M.dom_eq _ _).mp (cost_dom_of_elig (cancelAt_mem_true_iff.mp hct).2.1)
        · rw [contrib_of_lt hni]; trivial
    intro n
    exact key (x+1) n (by omega)

