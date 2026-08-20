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


theorem cancelAt_mem_true_iff {i x : ℕ} :
    true ∈ cancelAt M r C i x ↔
      i ≤ x ∧ true ∈ elig M r C i x ∧ true ∈ noElig M r C i x := by
  unfold cancelAt
  by_cases hix : i ≤ x
  · rw [(by simp [hix] : decide (i ≤ x) = true)]
    simp only [cond_true, Part.mem_bind_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨e, he, t, ht, hand⟩
      have he' : e = true := by cases e <;> simp_all
      have ht' : t = true := by cases t <;> simp_all
      subst he'; subst ht'
      exact ⟨hix, he, ht⟩
    · rintro ⟨-, he, ht⟩
      exact ⟨true, he, true, ht, rfl⟩
  · rw [(by simp [hix] : decide (i ≤ x) = false)]
    simp only [cond_false, Part.mem_some_iff]
    constructor
    · intro h; exact absurd h.symm Bool.false_ne_true
    · rintro ⟨h, -⟩; exact absurd h hix

