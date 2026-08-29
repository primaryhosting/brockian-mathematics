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

theorem card_fiber_eq_card_stabilizer_fiber (x y : X) (hxy : ∃ g : G, g • x = y) :
    #{g : G | g • x = y} = #{g : G | g • x = x} := by
  obtain ⟨g₀, hg₀⟩ := hxy
  refine Finset.card_nbij (fun g => g₀⁻¹ * g) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, ← hg₀, inv_smul_smul]
  · intro a _ b _ hab
    exact mul_left_cancel hab
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg
    refine ⟨g₀ * g, ?_, ?_⟩
    · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      rw [mul_smul, hg, hg₀]
    · simp

/-- Counting `G` fiberwise over the orbit map `g ↦ g • x`. -/
