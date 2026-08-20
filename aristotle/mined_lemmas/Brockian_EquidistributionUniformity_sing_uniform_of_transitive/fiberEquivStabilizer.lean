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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- For a transitive action, the fiber `{g | g • x = y}` over any point `y` is in bijection
with the stabilizer of `x`: the map `g ↦ g₀⁻¹ * g` (where `g₀ • x = y`) is a bijection from the
fiber onto `stabilizer G x`. -/

def fiberEquivStabilizer (x y : X) (g₀ : G) (hg₀ : g₀ • x = y) :
    {g : G // g • x = y} ≃ stabilizer G x where
  toFun g := ⟨g₀⁻¹ * g.1, by
    simp only [mem_stabilizer_iff, mul_smul, g.2, ← hg₀, inv_smul_smul]⟩
  invFun h := ⟨g₀ * h.1, by
    have h' : h.1 • x = x := h.2
    rw [mul_smul, h', hg₀]⟩
  left_inv g := by simp
  right_inv h := by simp

/-- **Uniformity of singleton fibers for a transitive action.**

If a group `G` acts transitively on `X`, then for every pair of points `x y : X` the set of
group elements carrying `x` to `y` satisfies `#{g | g • x = y} * #X = #G`; in particular its
cardinality does not depend on `x` and `y`.

In probabilistic terms, pushing the uniform distribution on a finite group `G` forward along
`g ↦ g • x` gives the uniform distribution on `X`: every singleton `{y}` receives the same mass.

This is the orbit–stabilizer theorem
(`MulAction.index_stabilizer_of_transitive` together with `Subgroup.card_mul_index`)
combined with the coset description of the fibers. -/
