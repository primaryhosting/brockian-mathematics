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

theorem card_group_eq_card_mul_card_stabilizer_fiber
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    Fintype.card G = Fintype.card X * #{g : G | g • x = x} := by
  have h : (Finset.univ : Finset G).card
      = ∑ y ∈ (Finset.univ : Finset X), #{g ∈ (Finset.univ : Finset G) | g • x = y} :=
    Finset.card_eq_sum_card_fiberwise (fun g _ => Finset.mem_univ (g • x))
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun y _ => card_fiber_eq_card_stabilizer_fiber x y (htrans x y)),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Equidistribution of a transitive symmetry group.**

If a finite group `G` acts transitively on a finite set `X`, then for any point `x : X` and any
subset `S ⊆ X`, the group elements sending `x` into `S` are exactly a `#S / #X` fraction of `G`:
`#{g | g • x ∈ S} * #X = #S * #G`.

Thus the orbit map `g ↦ g • x` equidistributes `G` over `X`; no additional hypothesis beyond
transitivity is needed. -/
