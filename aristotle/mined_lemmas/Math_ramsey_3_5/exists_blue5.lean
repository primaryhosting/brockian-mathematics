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

theorem exists_blue5 (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S)
    (T : Finset V) (hT : 14 ≤ T.card) : ∃ S ⊆ T, S.card = 5 ∧ Mono c false S := by
  obtain ⟨T', hT'T, hT'⟩ := Finset.exists_subset_card_eq hT
  have hv' : T'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hv'
  set E := T'.erase v with hEdef
  set R := E.filter (fun u => c v u = true) with hRdef
  set B := E.filter (fun u => c v u = false) with hBdef
  have hEcard : E.card = 13 := by rw [hEdef, Finset.card_erase_of_mem hv, hT']
  have hBeq : B = E.filter (fun u => ¬ (c v u = true)) := by ext x; simp [hBdef]
  have hsum : R.card + B.card = 13 := by
    rw [← hEcard, hBeq, hRdef]
    exact Finset.card_filter_add_card_filter_not _
  have hRE : R ⊆ E := Finset.filter_subset _ _
  have hBE : B ⊆ E := Finset.filter_subset _ _
  have hET : E ⊆ T' := Finset.erase_subset _ _
  by_cases hcase : 5 ≤ R.card
  · obtain ⟨S, hSR, hS5⟩ := Finset.exists_subset_card_eq hcase
    have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hRE (hSR h))).1 rfl
    exact ⟨S, fun x hx => hT'T (hET (hRE (hSR hx))), hS5,
      mono_false_of_red_nbhd hsymm hno3 hvS (fun u hu => (Finset.mem_filter.mp (hSR hu)).2)⟩
  · obtain ⟨S, hSB, hS4, hSm⟩ := exists_blue4 hsymm hno3 B (by omega)
    have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hBE (hSB h))).1 rfl
    refine ⟨insert v S, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hT'T hv
      · exact hT'T (hET (hBE (hSB hx)))
    · rw [Finset.card_insert_of_notMem hvS, hS4]
    · exact mono_insert hsymm hSm (fun u hu => (Finset.mem_filter.mp (hSB hu)).2) hvS

end General

/-- The upper bound `R(3,5) ≤ 14`. -/
