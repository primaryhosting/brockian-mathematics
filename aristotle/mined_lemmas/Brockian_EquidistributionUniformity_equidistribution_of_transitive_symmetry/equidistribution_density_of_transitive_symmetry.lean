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

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian
namespace EquidistributionUniformity

open Finset

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- All fibers of the orbit map `g ↦ g • x` have the same cardinality, namely that of the
stabilizer fiber `{g | g • x = x}`, provided the point `y` lies in the orbit of `x`. -/

theorem equidistribution_density_of_transitive_symmetry
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) (S : Finset X) :
    (#{g : G | g • x ∈ S} : ℚ) / (Fintype.card G : ℚ)
      = (S.card : ℚ) / (Fintype.card X : ℚ) := by
  have hX : (0 : ℚ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
  have hG : (0 : ℚ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
  have h := equidistribution_of_transitive_symmetry htrans x S
  have h' : (#{g : G | g • x ∈ S} : ℚ) * (Fintype.card X : ℚ)
      = (S.card : ℚ) * (Fintype.card G : ℚ) := by exact_mod_cast h
  field_simp
  linarith [h']

/-- Version of `equidistribution_of_transitive_symmetry` phrased with Mathlib's
`MulAction.IsPretransitive` typeclass. -/
