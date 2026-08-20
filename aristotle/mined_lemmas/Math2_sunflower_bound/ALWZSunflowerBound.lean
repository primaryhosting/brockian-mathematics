/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
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

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower T c` says that the family `T` is a *sunflower* with *core* `c`:
any two distinct members of `T` intersect exactly in `c`.  (The members of `T`
minus the core are the *petals*, and they are pairwise disjoint.) -/

def ALWZSunflowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (β : Type) [DecidableEq β] (w r : ℕ), 2 ≤ w → 1 ≤ r →
    ∀ F : Finset (Finset β), (∀ A ∈ F, A.card = w) →
      (C * r * Real.log w) ^ w < (F.card : ℝ) →
        ∃ T ⊆ F, T.card = r ∧ ∃ c : Finset β, IsSunflower T c

end Math2

