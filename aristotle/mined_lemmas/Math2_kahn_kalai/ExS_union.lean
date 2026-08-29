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

lemma ExS_union (s : Finset X) (p q : ℝ) :
    ∀ f : Finset X → ℝ,
      ExS s p (fun W => ExS s q (fun V => f (W ∪ V))) = ExS s (p + q - p * q) f := by
  classical
  induction s using Finset.induction_on with
  | empty => intro f; simp [ExS_empty]
  | insert a s ha ih =>
      intro f
      have key : ∀ W : Finset X,
          ExS (insert a s) q (fun V => f (insert a W ∪ V))
            = ExS s q (fun V => f (insert a (W ∪ V))) := by
        intro W
        rw [ExS_insert ha]
        have e1 : (fun V => f (insert a W ∪ insert a V)) = fun V => f (insert a (W ∪ V)) := by
          funext V
          congr 1
          rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem]
        have e2 : (fun V => f (insert a W ∪ V)) = fun V => f (insert a (W ∪ V)) := by
          funext V
          congr 1
          rw [Finset.insert_union]
        rw [e1, e2]
        ring
      have key2 : ∀ W : Finset X,
          ExS (insert a s) q (fun V => f (W ∪ V))
            = q * ExS s q (fun V => f (insert a (W ∪ V)))
              + (1 - q) * ExS s q (fun V => f (W ∪ V)) := by
        intro W
        rw [ExS_insert ha]
        have e1 : (fun V => f (W ∪ insert a V)) = fun V => f (insert a (W ∪ V)) := by
          funext V
          congr 1
          rw [Finset.union_insert]
        rw [e1]
      rw [ExS_insert ha]
      simp only [key, key2]
      rw [ExS_add s p (fun W => q * ExS s q fun V => f (insert a (W ∪ V)))
        (fun W => (1 - q) * ExS s q fun V => f (W ∪ V))]
      rw [ExS_const_mul s p q (fun W => ExS s q fun V => f (insert a (W ∪ V))),
        ExS_const_mul s p (1 - q) (fun W => ExS s q fun V => f (W ∪ V))]
      rw [ih (fun U => f (insert a U)), ih f]
      rw [ExS_insert ha (p + q - p * q) f]
      ring

/-- `Ex` is `ExS` over the whole ground set. -/
