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
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings (strict total orders) -/

/-- A *ranking* of the alternatives `A` is a strict total order: an irreflexive,
transitive and total (trichotomous) relation.  `r x y` means "`x` is strictly
preferred to `y`". -/
structure IsRanking {A : Type*} (r : A → A → Prop) : Prop where
  irrefl : ∀ x, ¬ r x x
  trans : ∀ {x y z}, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x

namespace IsRanking

variable {A : Type*} {r : A → A → Prop}


theorem iff_pair_swap {p q : A → A → Prop} (hp : IsRanking p) (hq : IsRanking q) {x y : A}
    (h1 : p y x) (h2 : q y x) : (p x y ↔ q x y) ∧ (p y x ↔ q y x) :=
  ⟨iff_of_false (hp.asymm h1) (hq.asymm h2), iff_of_true h1 h2⟩

section GroupContraction

variable {F : (V → A → A → Prop) → (A → A → Prop)} [DecidableEq V]

/-- **Group contraction**: if a coalition `S` is decisive and `i ∈ S`, then either `{i}`
or `S \ {i}` is almost decisive for some ordered pair. -/
