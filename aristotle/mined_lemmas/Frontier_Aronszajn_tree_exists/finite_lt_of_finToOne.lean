import Mathlib
/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
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

open Set Cardinal Ordinal
open scoped Ordinal Cardinal

namespace Frontier

/-! ## Countable ordinals -/

/-- The set of ordinals below `a` is countable exactly when `a < ω₁`. -/

theorem finite_lt_of_finToOne {a : Ordinal.{0}} {f : Ordinal.{0} → ℕ}
    (hf : ∀ k : ℕ, {ξ | ξ < a ∧ f ξ = k}.Finite) (m : ℕ) : {ξ | ξ < a ∧ f ξ < m}.Finite := by
  refine Set.Finite.subset ((Set.finite_Iio m).biUnion (fun k _ => hf k)) ?_
  rintro ξ ⟨h1, h2⟩
  exact Set.mem_biUnion h2 ⟨h1, rfl⟩

