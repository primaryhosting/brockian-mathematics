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


theorem maxK_ge (m u L : ℕ) (hL : L ≤ u) {K : ℕ} (hK : K ∈ maxK M C m u)
    {c : ℕ} (hc : c ∈ M.cost (patchCode C m L) u) : c ≤ K := by
  have key : ∀ j, ∀ K ∈ (Nat.rec (motive := fun _ => Part ℕ)
      (M.cost (patchCode C m 0) u)
      (fun L ih => ih.bind fun v => (M.cost (patchCode C m (L+1)) u).map (fun w => max v w))
      j), L ≤ j → c ≤ K := by
    intro j
    induction j with
    | zero =>
      intro K hK hLj
      have hL0 : L = 0 := by omega
      subst hL0
      exact le_of_eq (Part.mem_unique hc hK)
    | succ k ih =>
      intro K hK hLj
      simp only [Part.mem_bind_iff, Part.mem_map_iff] at hK
      obtain ⟨v, hv, w, hw, rfl⟩ := hK
      rcases Nat.lt_or_ge L (k+1) with hlt | hge
      · exact le_trans (ih v hv (by omega)) (le_max_left _ _)
      · have hLk : L = k + 1 := by omega
        subst hLk
        exact le_trans (le_of_eq (Part.mem_unique hc hw)) (le_max_right _ _)
  exact key u K hK hL

