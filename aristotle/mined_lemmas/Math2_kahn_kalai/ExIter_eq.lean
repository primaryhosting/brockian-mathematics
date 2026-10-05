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
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Defs

/-!
Elementary finite-probability toolkit for `p`-random subsets: the expectation `Ex p f`,
the fact that the weights sum to one, and the "union of independent random sets" identity.
-/

namespace Math2

open Finset

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The expectation of `f` at a `p`-random subset of the ground set `s`. -/

lemma ExIter_eq (p : ℝ) : ∀ (k : ℕ) (f : Finset X → ℝ),
    ExIter p k f = Ex (1 - (1 - p) ^ k) f := by
  intro k
  induction k with
  | zero => intro f; simp [ExIter, Ex_zero_param]
  | succ k ih =>
      intro f
      rw [ExIter]
      have : (fun W => ExIter p k (fun V => f (W ∪ V)))
          = fun W => Ex (1 - (1 - p) ^ k) (fun V => f (W ∪ V)) := by
        funext W; rw [ih]
      rw [this, Ex_union]
      congr 1
      ring

end Math2

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham).

Throughout, `X` is a finite ground set, subsets of `X` are elements of `Finset X`, and a
*hypergraph* (or family) on `X` is an element of `Finset (Finset X)`.
-/

namespace Math2

open Finset

open scoped Classical

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The weight of `W` under the product measure `μ_p` on subsets of `X`:
`μ_p({W}) = p ^ |W| * (1-p) ^ |X \ W|`. -/
