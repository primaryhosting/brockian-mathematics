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

namespace Brockian
namespace EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The *singular transport set* of the pair `(x, y)`: the set of group elements that move the
point `x` to the point `y`. -/

lemma transportSet_equiv_stabilizer {x y : X} {g₀ : G} (hg₀ : g₀ • x = y) :
    Nonempty (transportSet G x y ≃ stabilizer G x) := by
  refine ⟨⟨fun g => ⟨g₀⁻¹ * (g : G), ?_⟩, fun h => ⟨g₀ * (h : G), ?_⟩, ?_, ?_⟩⟩
  · have hg : (g : G) • x = y := g.2
    simp [MulAction.mem_stabilizer_iff, mul_smul, hg, ← hg₀]
  · have hh : (h : G) • x = x := h.2
    simp [mem_transportSet, mul_smul, hh, hg₀]
  · rintro ⟨g, hg⟩
    ext
    simp
  · rintro ⟨h, hh⟩
    ext
    simp

/-- The singular count of `(x, y)` equals the cardinality of the stabilizer of `x`, for a
transitive action. -/
