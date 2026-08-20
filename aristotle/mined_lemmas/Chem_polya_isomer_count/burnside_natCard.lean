/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open MulAction

attribute [local instance] arrowAction

section

variable {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [Fintype P] [MulAction G P]
variable {C : Type*} [Fintype C]

/-- Burnside's lemma, phrased with `Nat.card`. -/

lemma burnside_natCard {α : Type*} [Fintype α] [MulAction G α] :
    Nat.card (orbitRel.Quotient G α) * Nat.card G
      = ∑ g : G, Nat.card (fixedBy α g) := by
  classical
  letI : ∀ g : G, Fintype (fixedBy α g) := fun g => Fintype.ofFinite _
  letI : Fintype (orbitRel.Quotient G α) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (α := G) (β := α)
  simp only [← Nat.card_eq_fintype_card] at h
  simpa using h.symm

omit [Fintype G] [Fintype P] [Fintype C] in
/-- A coloring fixed by `g` is constant along the `⟨g⟩`-orbits. -/
