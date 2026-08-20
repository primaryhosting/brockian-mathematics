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


theorem acc_ge_contrib {n x i : ℕ} (hi : i ≤ x) {v : ℕ} (hv : v ∈ acc M r C n x)
    {c : ℕ} (hc : c ∈ contrib M r C n x i) : c ≤ v := by
  have key : ∀ j, ∀ v ∈ (Nat.rec (motive := fun _ => Part ℕ)
      (contrib M r C n x 0)
      (fun k ih => ih.bind fun v => (contrib M r C n x (k+1)).map fun w => max v w) j),
      i ≤ j → c ≤ v := by
    intro j
    induction j with
    | zero =>
      intro v hv hij
      have hi0 : i = 0 := by omega
      subst hi0
      exact le_of_eq (Part.mem_unique hc hv)
    | succ k ih =>
      intro V hV hij
      simp only [Part.mem_bind_iff, Part.mem_map_iff] at hV
      obtain ⟨v, hv, w, hw, rfl⟩ := hV
      rcases Nat.lt_or_ge i (k+1) with hlt | hge
      · exact le_trans (ih v hv (by omega)) (le_max_left _ _)
      · have hik : i = k + 1 := by omega
        subst hik
        exact le_trans (le_of_eq (Part.mem_unique hc hw)) (le_max_right _ _)
  exact key x v hv hi

