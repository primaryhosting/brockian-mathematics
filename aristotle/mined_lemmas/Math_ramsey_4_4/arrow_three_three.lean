/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The two-colour Ramsey number `R(4,4)` equals `18`.

Mathlib (at the pinned revision) contains no theory of Ramsey numbers, so the whole
argument is developed here:

* the classical upper bound `R(p+1,q+1) ≤ R(p,q+1) + R(p+1,q)` (`Math.arrow_step`),
* `R(3,3) ≤ 6` and, via the parity/degree argument, `R(3,4) ≤ 9`
  (`Math.arrow_three_three`, `Math.arrow_three_four`), giving `R(4,4) ≤ 18`,
* the Paley graph on 17 vertices, which has neither a 4-clique nor a 4-element
  independent set, giving `R(4,4) > 17`.
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

/-! ## A relation-theoretic formulation of Ramsey's theorem for two colours -/

variable {V : Type*}

/-- A finite set `t` is homogeneous for the relation `r` if all distinct pairs of elements
of `t` are related by `r`. -/

lemma arrow_three_three (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V)
    (hS : 6 ≤ S.card) : Arrow r S 3 3 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega : 0 < S.card)
  have h := arrow_step (r := r) (p := 2) (q := 2) (n₁ := 3) (n₂ := 3) hsymm
    (fun T hT => arrow_two_left r hsymm T hT)
    (fun T hT => arrow_two_right r hsymm T hT) hne (by omega)
  simpa using h

/-- Parity: the sum of a symmetric weight function with vanishing diagonal over a square
is even. -/
