/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

open Finset Pointwise

/-- The two translated copies `A + max B` and `min A + B` both sit inside `A + B`. -/
private lemma union_translates_subset {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.max' hB)) ∪ (B.image (fun b => A.min' hA + b)) ⊆ A + B := by
  intro x hx
  rcases Finset.mem_union.1 hx with hx | hx
  · rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
    exact Finset.add_mem_add ha (B.max'_mem hB)
  · rcases Finset.mem_image.1 hx with ⟨b, hb, rfl⟩
    exact Finset.add_mem_add (A.min'_mem hA) hb

/-- The two translated copies meet exactly in the single point `min A + max B`. -/
private lemma inter_translates {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.max' hB)) ∩ (B.image (fun b => A.min' hA + b))
      = {A.min' hA + B.max' hB} := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.1 hx with ⟨h1, h2⟩
    rcases Finset.mem_image.1 h1 with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.1 h2 with ⟨b, hb, hab⟩
    have ha' : A.min' hA ≤ a := A.min'_le a ha
    have hb' : b ≤ B.max' hB := B.le_max' b hb
    have : a = A.min' hA := by omega
    simp [this]
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_inter.2
      ⟨Finset.mem_image.2 ⟨A.min' hA, A.min'_mem hA, rfl⟩,
       Finset.mem_image.2 ⟨B.max' hB, B.max'_mem hB, rfl⟩⟩

/-- **Sumset lower bound over the integers** (the Cauchy–Davenport analogue / base case of
Freiman's lemma): for finite nonempty sets `A`, `B` of integers,
`|A| + |B| - 1 ≤ |A + B|`. -/
theorem sumset_lower_bound {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  set X := A.image (· + B.max' hB)
  set Y := B.image (fun b => A.min' hA + b)
  have hXcard : X.card = A.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hYcard : Y.card = B.card :=
    Finset.card_image_of_injective _ (add_right_injective _)
  have hinter : (X ∩ Y).card = 1 := by
    rw [inter_translates hA hB]; simp
  have hunion : (X ∪ Y).card + (X ∩ Y).card = X.card + Y.card :=
    Finset.card_union_add_card_inter X Y
  have hsub : (X ∪ Y).card ≤ (A + B).card :=
    Finset.card_le_card (union_translates_subset hA hB)
  omega

end AdditiveComb

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

