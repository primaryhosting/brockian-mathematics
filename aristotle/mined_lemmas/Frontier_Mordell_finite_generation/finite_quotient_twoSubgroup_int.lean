/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
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

set_option grind.warning false

namespace Frontier

/-! ## The descent machinery

Mordell's theorem states that the group `E(ℚ)` of rational points of an elliptic curve over `ℚ`
is finitely generated.  Its classical proof has two inputs:

* the *weak Mordell–Weil theorem*: the quotient `E(ℚ)/2E(ℚ)` is finite;
* the *theory of heights*: there is a height function `h : E(ℚ) → ℝ` satisfying the three
  standard properties recorded in `Frontier.HeightData` below.

The purely group-theoretic step which combines these two inputs into finite generation is the
*descent theorem*, `Frontier.fg_of_quotient_two_finite_of_heightData`, which is proved here in
full generality for an arbitrary additive commutative group.  The target theorem
`Frontier.Mordell_finite_generation` is the resulting Lean-checked reduction of Mordell's

lemma finite_quotient_twoSubgroup_int : Finite (ℤ ⧸ twoSubgroup ℤ) := by
  refine Finite.of_surjective
    (fun b : Bool => (QuotientAddGroup.mk (s := twoSubgroup ℤ) (if b then 1 else 0))) ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H n =>
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨false, QuotientAddGroup.eq.mpr (mem_twoSubgroup_iff.mpr ⟨k, ?_⟩)⟩
      simp only [Bool.false_eq_true, if_false]
      omega
    · refine ⟨true, QuotientAddGroup.eq.mpr (mem_twoSubgroup_iff.mpr ⟨k, ?_⟩)⟩
      simp only [if_true]
      omega

/-- The squared absolute value is a height function on `ℤ`. -/
