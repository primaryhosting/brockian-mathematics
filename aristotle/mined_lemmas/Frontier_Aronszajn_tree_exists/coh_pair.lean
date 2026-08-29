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

theorem coh_pair {x y : Ordinal.{0}} (hx : Inv x) (hy : Inv y) :
    {ξ | ξ < x ∧ ξ < y ∧ E x ξ ≠ E y ξ}.Finite := by
  rcases lt_trichotomy x y with h | h | h
  · refine Set.Finite.subset (hy.2.2 x h) ?_
    rintro ξ ⟨h1, _, h3⟩
    exact ⟨h1, fun hc => h3 hc.symm⟩
  · subst h
    convert Set.finite_empty
    ext ξ
    simp
  · refine Set.Finite.subset (hx.2.2 y h) ?_
    rintro ξ ⟨_, h2, h3⟩
    exact ⟨h2, h3⟩

