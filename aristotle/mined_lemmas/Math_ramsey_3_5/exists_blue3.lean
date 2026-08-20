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

theorem exists_blue3 (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S)
    (T : Finset V) (hT : 6 ≤ T.card) : ∃ S ⊆ T, S.card = 3 ∧ Mono c false S := by
  obtain ⟨v, hv⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hEcard : (T.erase v).card = T.card - 1 := Finset.card_erase_of_mem hv
  set E := T.erase v with hEdef
  set R := E.filter (fun u => c v u = true) with hRdef
  set B := E.filter (fun u => c v u = false) with hBdef
  have hBeq : B = E.filter (fun u => ¬ (c v u = true)) := by
    ext x; simp [hBdef]
  have hsum : R.card + B.card = E.card := by
    rw [hBeq, hRdef]
    exact Finset.card_filter_add_card_filter_not _
  have hRE : R ⊆ E := Finset.filter_subset _ _
  have hBE : B ⊆ E := Finset.filter_subset _ _
  have hET : E ⊆ T := Finset.erase_subset _ _
  by_cases hcase : 3 ≤ R.card
  · obtain ⟨S, hSR, hS3⟩ := Finset.exists_subset_card_eq hcase
    have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hRE (hSR h))).1 rfl
    exact ⟨S, fun x hx => hET (hRE (hSR hx)), hS3,
      mono_false_of_red_nbhd hsymm hno3 hvS (fun u hu => (Finset.mem_filter.mp (hSR hu)).2)⟩
  · have hB3 : 3 ≤ B.card := by omega
    obtain ⟨S, hSB, hS3⟩ := Finset.exists_subset_card_eq hB3
    by_cases hpair : ∃ u ∈ S, ∃ w ∈ S, u ≠ w ∧ c u w = false
    · obtain ⟨u, hu, w, hw, huw, hcuw⟩ := hpair
      have hvu : v ≠ u := Ne.symm (Finset.mem_erase.mp (hBE (hSB hu))).1
      have hvw : v ≠ w := Ne.symm (Finset.mem_erase.mp (hBE (hSB hw))).1
      have hcvu : c v u = false := (Finset.mem_filter.mp (hSB hu)).2
      have hcvw : c v w = false := (Finset.mem_filter.mp (hSB hw)).2
      refine ⟨{v, u, w}, ?_, Finset.card_eq_three.mpr ⟨v, u, w, hvu, hvw, huw, rfl⟩,
        mono_triple hsymm hcvu hcvw hcuw⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact hET (hBE (hSB hu))
      · exact hET (hBE (hSB hw))
    · exfalso
      refine hno3 S hS3 ?_
      intro u hu w hw huw
      by_contra hne
      refine hpair ⟨u, hu, w, hw, huw, ?_⟩
      cases hc : c u w with
      | false => rfl
      | true => exact absurd hc hne

/-- `R(3,4) ≤ 9`: with no red triangle, any 9 vertices contain a blue set of size 4. -/
