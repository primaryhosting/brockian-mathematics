import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Filter

section RamseyConstruction

/-- Pick an element of a set of naturals (junk value `0` if the set is empty). -/

lemma ramseySets_mem (U : Ultrafilter ℕ) (hcof : ∀ N : ℕ, {m : ℕ | N < m} ∈ U)
    (hA : A ∈ U) (hAcol : ∀ n ∈ A, {m : ℕ | c n m = k} ∈ U) :
    ∀ n, ramseySets c k A n ∈ U ∧ ramseySets c k A n ⊆ A := by
  intro n
  induction n with
  | zero => exact ⟨hA, subset_rfl⟩
  | succ n ih =>
    obtain ⟨hmem, hsub⟩ := ih
    have hne : (ramseySets c k A n).Nonempty := Ultrafilter.nonempty_of_mem hmem
    have hpick : pick (ramseySets c k A n) ∈ ramseySets c k A n := pick_mem hne
    have hcol : {m : ℕ | c (pick (ramseySets c k A n)) m = k} ∈ U := hAcol _ (hsub hpick)
    refine ⟨?_, (ramseySets_succ_subset c k A n).trans hsub⟩
    have : ramseySets c k A (n + 1)
        = ramseySets c k A n ∩ ({m : ℕ | c (pick (ramseySets c k A n)) m = k}
          ∩ {m : ℕ | pick (ramseySets c k A n) < m}) := by
      rw [ramseySets]
      ext x
      simp
    rw [this]
    exact Filter.inter_mem hmem (Filter.inter_mem hcol (hcof _))

