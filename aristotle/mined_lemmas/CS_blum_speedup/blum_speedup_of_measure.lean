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


theorem blum_speedup_of_measure (M : BlumMeasure) (r : ℕ → ℕ) (hr : Computable r) :
    ∃ f : ℕ → ℕ, Computable f ∧
      ∀ e : Code, e.eval = (fun x => Part.some (f x)) →
        ∃ e' : Code, e'.eval = (fun x => Part.some (f x)) ∧
          ∀ᶠ x in Filter.atTop, ∃ a ∈ M.cost e' x, ∃ b ∈ M.cost e x, r a ≤ b := by
  have hR : Computable (rSup r) := rSup_computable hr
  refine ⟨bigFun M hR, bigFun_computable M hR, ?_⟩
  intro e he
  have hie : ofNat Code (encode e) = e := Denumerable.ofNat_encode e
  obtain ⟨L, hL⟩ := exists_patch_length M hR (encode e + 1)
  refine ⟨patchCode (selfCode M hR) (encode e + 1) L, eval_patchCode_eq M hR hL, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max (encode e) L)] with x hx
  have hdom_e' : (M.cost (patchCode (selfCode M hR) (encode e + 1) L) x).Dom := by
    refine (M.dom_eq _ _).mpr ?_
    rw [eval_patchCode_eq M hR hL]
    trivial
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hdom_e'
  have hdom_e : (M.cost e x).Dom := by
    refine (M.dom_eq _ _).mpr ?_
    rw [he]
    trivial
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hdom_e
  refine ⟨a, ha, b, hb, ?_⟩
  have hne : false ∈ elig M (rSup r) (selfCode M hR) (encode e) x :=
    not_elig_of_computes M hR (by rw [hie, he]) x (by omega)
  have hb' : b ∈ M.cost (ofNat Code (encode e)) x := by rw [hie]; exact hb
  obtain ⟨K, hK, hKb⟩ := cost_gt_of_not_elig hne hb'
  have haK : a ≤ K := maxK_ge (encode e + 1) x L (by omega) hK ha
  calc r a ≤ rSup r a := le_rSup r a
    _ ≤ rSup r K := rSup_mono r haK
    _ ≤ b := le_of_lt hKb

end CS

/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Strong

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

/-! ## A Blum measure exhibiting speedup -/

/-- The cost assigned to the `n`-th padding program at input `x`. -/
