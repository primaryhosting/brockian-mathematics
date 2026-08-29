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

open scoped BigOperators
open scoped Classical

namespace Brockian
namespace EquidistributionUniformity

variable {G X : Type*} [Group G] [MulAction G X]

/-- An invariant function on a set carrying a transitive action is constant. -/

theorem eq_of_invariant_of_pretransitive [MulAction.IsPretransitive G X]
    {M : Type*} (f : X → M) (hf : ∀ (g : G) (x : X), f (g • x) = f x) (x y : X) :
    f x = f y := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  rw [← hg, hf]

/-- **Equidistribution of transitive symmetry.**
If a group `G` acts transitively on a finite set `X` and `f : X → ℝ` is a `G`-invariant
weighting with total mass `1`, then `f` is the uniform distribution:
`f x = 1 / card X` for every `x`. -/
