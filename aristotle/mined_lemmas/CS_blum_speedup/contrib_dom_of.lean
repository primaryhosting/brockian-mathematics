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


theorem contrib_dom_of {n x i : ℕ} (h : (cancelAt M r C i x).Dom)
    (hev : true ∈ cancelAt M r C i x → ((ofNat Code i).eval x).Dom) :
    (contrib M r C n x i).Dom := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
  cases b with
  | false => rw [contrib_eq_of_not_cancel hb]; trivial
  | true =>
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp (hev hb)
    by_cases hn : n ≤ i
    · exact Part.dom_iff_mem.mpr ⟨w + 1, contrib_mem_of_cancel hn hb hw⟩
    · rw [contrib_of_lt hn]; trivial

