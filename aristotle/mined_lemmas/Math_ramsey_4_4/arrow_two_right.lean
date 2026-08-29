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

lemma arrow_two_right (r : V → V → Prop) (hsymm : ∀ x y, r x y → r y x) (S : Finset V) {p : ℕ}
    (hcard : p ≤ S.card) : Arrow r S p 2 :=
  arrow_swap (arrow_two_left (fun a b => ¬ r a b) (fun _ _ h hc => h (hsymm _ _ hc)) S hcard)

/-- The classical induction step `R(p+1, q+1) ≤ R(p, q+1) + R(p+1, q)`. -/
