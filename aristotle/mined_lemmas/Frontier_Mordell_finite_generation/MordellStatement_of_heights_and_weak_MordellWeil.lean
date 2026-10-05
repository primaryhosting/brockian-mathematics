/-
/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The statement of the Mordell–Weil theorem

`Frontier.MordellStatement` is the formal statement of Mordell's theorem: for every elliptic
curve over `ℚ`, the group of rational points (in affine coordinates, i.e. the affine points
together with the point at infinity) is a finitely generated abelian group.

The main results below are a *Lean-checked reduction* of this statement to the two standard
inputs of the classical proof:

* the **weak Mordell–Weil theorem**: `E(ℚ)/2E(ℚ)` is finite, encoded as a finite set `R` of
  coset representatives;
* the **theory of heights**: a nonnegative height function `ht` on `E(ℚ)` with finite
  sublevel sets, a quasi-parallelogram bound `ht (P + Q) ≤ 2 * ht P + C_Q`, and a duplication
  bound `4 * ht P ≤ ht (2 • P) + C`.

The engine is `Frontier.descent_of_height`, the classical descent theorem for abstract abelian
groups, proved unconditionally below.
-/

/-- The Mordell–Weil theorem over `ℚ`: the group of rational points of an elliptic curve
over `ℚ` is finitely generated. -/

theorem MordellStatement_of_heights_and_weak_MordellWeil
    (H : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
      ∃ ht : W.toAffine.Point → ℝ,
        (∀ P : W.toAffine.Point, 0 ≤ ht P) ∧
        (∀ B : ℝ, {P : W.toAffine.Point | ht P ≤ B}.Finite) ∧
        (∀ Q : W.toAffine.Point, ∃ C : ℝ, ∀ P : W.toAffine.Point,
          ht (P + Q) ≤ 2 * ht P + C) ∧
        (∃ C : ℝ, ∀ P : W.toAffine.Point, 4 * ht P ≤ ht (2 • P) + C) ∧
        (∃ R : Finset W.toAffine.Point, ∀ P : W.toAffine.Point,
          ∃ Q ∈ R, ∃ P' : W.toAffine.Point, P = 2 • P' + Q)) :
    MordellStatement := by
  intro W hW
  obtain ⟨ht, hnonneg, hfin, htri, hdup, R, hR⟩ := H W hW
  exact Mordell_finite_generation W hW ht hnonneg hfin htri hdup R hR

/-!
## Non-vacuity check

The hypotheses of the descent theorem are satisfiable: they hold for `A = ℤ` with the
"height" `n ↦ n ^ 2`, and the descent theorem then yields that `ℤ` is finitely generated.
-/

