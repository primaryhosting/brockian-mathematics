import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/

theorem exists_blue4 (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S)
    (T : Finset V) (hT : 9 ≤ T.card) : ∃ S ⊆ T, S.card = 4 ∧ Mono c false S := by
  obtain ⟨T', hT'T, hT'⟩ := Finset.exists_subset_card_eq hT
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ T', ((T'.erase v).filter (fun u => c v u = true)).card = 3 := by
    intro v hv
    set E := T'.erase v with hEdef
    set R := E.filter (fun u => c v u = true) with hRdef
    set B := E.filter (fun u => c v u = false) with hBdef
    have hEcard : E.card = 8 := by rw [hEdef, Finset.card_erase_of_mem hv, hT']
    have hBeq : B = E.filter (fun u => ¬ (c v u = true)) := by ext x; simp [hBdef]
    have hsum : R.card + B.card = 8 := by
      rw [← hEcard, hBeq, hRdef]
      exact Finset.card_filter_add_card_filter_not _
    have hRE : R ⊆ E := Finset.filter_subset _ _
    have hBE : B ⊆ E := Finset.filter_subset _ _
    have hET : E ⊆ T' := Finset.erase_subset _ _
    have hR4 : R.card ≤ 3 := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨S, hSR, hS4⟩ := Finset.exists_subset_card_eq (show 4 ≤ R.card by omega)
      have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hRE (hSR h))).1 rfl
      exact hcon S (fun x hx => hT'T (hET (hRE (hSR hx)))) hS4
        (mono_false_of_red_nbhd hsymm hno3 hvS (fun u hu => (Finset.mem_filter.mp (hSR hu)).2))
    have hB5 : B.card ≤ 5 := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨S, hSB, hS3, hSm⟩ := exists_blue3 hsymm hno3 B (by omega)
      have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hBE (hSB h))).1 rfl
      refine hcon (insert v S) ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hT'T hv
        · exact hT'T (hET (hBE (hSB hx)))
      · rw [Finset.card_insert_of_notMem hvS, hS3]
      · exact mono_insert hsymm hSm (fun u hu => (Finset.mem_filter.mp (hSB hu)).2) hvS
    omega
  have heven := even_sum_adj_card (fun x y => x ≠ y ∧ c x y = true)
    (fun x y h => ⟨Ne.symm h.1, by rw [hsymm]; exact h.2⟩) (by simp) T'
  have hrw : ∀ v ∈ T', (T'.filter (fun u => v ≠ u ∧ c v u = true)).card = 3 := by
    intro v hv
    rw [← key v hv]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, hne, hc⟩; exact ⟨⟨Ne.symm hne, hu⟩, hc⟩
    · rintro ⟨⟨hne, hu⟩, hc⟩; exact ⟨hu, Ne.symm hne, hc⟩
  rw [Finset.sum_congr rfl hrw, Finset.sum_const, hT'] at heven
  norm_num at heven

/-- `R(3,5) ≤ 14`: with no red triangle, any 14 vertices contain a blue set of size 5. -/
