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
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem dprodTree_ok {Q : (Assign → Bool) → Prop} (n : ℕ) (D : ℕ → GapData) (s : ℕ)
    (hD : ∀ i, (D i).Ok Q s) :
    ∀ (d off : ℕ), (dprodTree n D d off).Ok Q (9 ^ d * (s + 3))
  | 0, off => by simpa [dprodTree] using (hD off).mono (by omega)
  | (d + 1), off => by
      have h1 := dprodTree_ok n D s hD d off
      have h2 := dprodTree_ok n D s hD d (off + 2 ^ d)
      have hmul := dmul_ok (Q := Q) (s := 9 ^ d * (s + 3)) n h1 h2
      refine hmul.mono ?_
      have hp : (1 : ℕ) ≤ 9 ^ d := Nat.one_le_pow _ _ (by omega)
      have he : 9 ^ (d + 1) * (s + 3) = 8 * (9 ^ d * (s + 3)) + 9 ^ d * (s + 3) := by ring
      nlinarith [hp]

end GapData

end CS

/-
Basic framework for a formalization of Toda's theorem.

We work with a semantic notion of "computed by a small formula over a base class `Q`
of oracle predicates".  Inputs are (infinite) Boolean assignments `Assign = ℕ → Bool`;
an input of length `n` only uses the variables `0, …, n-1`, and witnesses are placed in
the variables `n, n+1, …`.
-/
import Mathlib

namespace CS

open scoped BigOperators

/-- An assignment of Boolean values to the variables `0, 1, 2, …`. -/
abbrev Assign := ℕ → Bool

/-! ### Polynomial bounds -/

/-- `s` is bounded by a polynomial. -/
