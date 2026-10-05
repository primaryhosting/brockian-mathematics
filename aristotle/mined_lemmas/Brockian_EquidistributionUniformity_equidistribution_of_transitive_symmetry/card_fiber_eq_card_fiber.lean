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
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Brockian.EquidistributionUniformity

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- If the group `G` acts transitively on `X`, then any two fibers of the orbit map
`g ↦ g • x₀` have the same cardinality: translating by a group element carrying `x` to `y`
is a bijection between the fibers. -/

lemma card_fiber_eq_card_fiber (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x₀ x y : X) :
    (Finset.univ.filter (fun g : G => g • x₀ = x)).card
      = (Finset.univ.filter (fun g : G => g • x₀ = y)).card := by
  obtain ⟨h, hh⟩ := htrans x y
  refine Finset.card_bij (fun g _ => h * g) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, hh]
  · intro a _ b _ hab
    exact mul_left_cancel hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨h⁻¹ * b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mul_smul, hb, ← hh, inv_smul_smul]
    · simp

/-- **Equidistribution of transitive symmetry.**  If a finite group `G` acts transitively on a
finite set `X`, then the orbit map `g ↦ g • x₀` distributes the group uniformly over `X`: every
point `x ∈ X` is hit by exactly `|G| / |X|` group elements.  Stated without division: the number
of `g ∈ G` with `g • x₀ = x`, times `|X|`, equals `|G|`.

The only assumption is transitivity of the action (together with finiteness); no further named
hypothesis is used, so the result is unconditional. -/
