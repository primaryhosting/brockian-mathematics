import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` lines to come first in a module, so the
required header block is placed immediately after the single `import Mathlib` line.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Codimension-one subsets -/

/-- Subsets of `S` of cardinality `S.card - 1` are exactly the sets `S.erase x` for `x ∈ S`;
hence counting them amounts to counting the vertices `x ∈ S` with the corresponding property. -/

lemma card_filter_powerset_erase (S : Finset V) (m : ℕ) (hS : S.card = m + 1)
    (P : Finset V → Prop) [DecidablePred P] :
    (S.powerset.filter (fun G => G.card = m ∧ P G)).card
      = (S.filter (fun x => P (S.erase x))).card := by
  have herase : ∀ x ∈ S, (S.erase x).card = m := by
    intro x hx
    rw [Finset.card_erase_of_mem hx, hS]
    omega
  have hinj : Set.InjOn (fun x => S.erase x) S := by
    intro x hx y hy h
    by_contra hne
    have hx' : x ∈ S.erase y := Finset.mem_erase.2 ⟨hne, hx⟩
    rw [← show S.erase x = S.erase y from h] at hx'
    exact Finset.notMem_erase x S hx'
  have hset : S.powerset.filter (fun G => G.card = m ∧ P G)
      = (S.filter (fun x => P (S.erase x))).image (fun x => S.erase x) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hGS, hGc, hGP⟩
      obtain ⟨x, hxS, hxG⟩ : ∃ x ∈ S, x ∉ G := by
        by_contra hcon
        push_neg at hcon
        have hsub : S ⊆ G := fun y hy => hcon y hy
        have := Finset.card_le_card hsub
        omega
      have hGe : G = S.erase x := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro y hy
          exact Finset.mem_erase.2 ⟨by rintro rfl; exact hxG hy, hGS hy⟩
        · rw [herase x hxS, hGc]
      exact ⟨x, ⟨hxS, hGe ▸ hGP⟩, hGe.symm⟩
    · rintro ⟨x, ⟨hxS, hxP⟩, rfl⟩
      exact ⟨Finset.erase_subset _ _, herase x hxS, hxP⟩
  rw [hset]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy h
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
  exact hinj hx.1 hy.1 h

/-! ### Images after deleting one vertex -/

