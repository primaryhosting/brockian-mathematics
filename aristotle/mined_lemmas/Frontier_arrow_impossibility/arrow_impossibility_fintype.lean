import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem arrow_impossibility_fintype {V : Type v} [Fintype V] :
    ¬ ∃ F : (V → Ranking (Fin 3)) → Ranking (Fin 3),
        Unanimous F ∧ IIA F ∧ (∀ i : V, ¬ IsDictator F i) :=
  arrow_impossibility finitelyMany_of_fintype

end Frontier

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u v

/-! ## Rankings (strict linear orders) -/

/-- A *ranking* of `α`: a strict linear order, described by its strict part `lt`. -/
structure Ranking (α : Type u) where
  /-- The strict preference relation: `lt x y` means "`x` is strictly preferred to `y`". -/
  lt : α → α → Prop
  /-- Transitivity. -/
  tr : ∀ {x y z : α}, lt x y → lt y z → lt x z
  /-- Totality: distinct alternatives are comparable. -/
  tot : ∀ x y : α, x ≠ y → lt x y ∨ lt y x
  /-- Asymmetry. -/
  asym : ∀ {x y : α}, lt x y → ¬ lt y x

namespace Ranking

variable {α : Type u} (R : Ranking α)

