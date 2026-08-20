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


theorem not_elig_of_computes (hr : Computable r) {i : ℕ}
    (hi : (ofNat Code i).eval = fun x => Part.some (bigFun M hr x)) :
    ∀ y, i ≤ y → false ∈ elig M r (selfCode M hr) i y := by
  classical
  intro y hiy
  by_contra hcon
  have htrue : true ∈ elig M r (selfCode M hr) i y := elig_true_of_not_false M hr i y hcon
  have hP : ∃ z, i ≤ z ∧ true ∈ elig M r (selfCode M hr) i z := ⟨y, hiy, htrue⟩
  obtain ⟨hiz, hz⟩ := Nat.find_spec hP
  have hno : true ∈ noElig M r (selfCode M hr) i (Nat.find hP) := by
    refine noElig_of ?_
    intro w hiw hwz
    refine elig_false_of_not_true M hr i w ?_
    intro hw
    exact absurd ⟨hiw, hw⟩ (Nat.find_min hP hwz)
  have hcanc : true ∈ cancelAt M r (selfCode M hr) i (Nat.find hP) :=
    cancelAt_mem_true_iff.mpr ⟨hiz, hz, hno⟩
  have hw : bigFun M hr (Nat.find hP) ∈ (ofNat Code i).eval (Nat.find hP) := by
    rw [hi]; exact Part.mem_some _
  have hc : bigFun M hr (Nat.find hP) + 1 ∈ contrib M r (selfCode M hr) 0 (Nat.find hP) i :=
    contrib_mem_of_cancel (Nat.zero_le i) hcanc hw
  have hle := acc_ge_contrib hiz (bigFun_mem M hr (Nat.find hP)) hc
  omega

/-- An index is cancelled at most at one stage. -/
