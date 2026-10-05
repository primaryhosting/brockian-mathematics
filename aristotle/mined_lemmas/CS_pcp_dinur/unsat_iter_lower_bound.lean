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

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- `iter f t g` is the `t`-fold iterate `f^[t] g`. -/

theorem unsat_iter_lower_bound (unsat : G → Nat) (amplify : G → G) (gap : Nat)
    (hamplify : ∀ g, min gap (2 * unsat g) ≤ unsat (amplify g)) :
    ∀ (t : Nat) (g : G), min gap (2 ^ t * unsat g) ≤ unsat (iter amplify t g) := by
  intro t
  induction t with
  | zero => intro g; simp; omega
  | succ t ih =>
    intro g
    have hstep : min gap (2 * unsat (iter amplify t g)) ≤ unsat (iter amplify (t + 1) g) := by
      rw [iter_succ]; exact hamplify _
    have ihg := ih g
    rcases Nat.le_total gap (2 ^ t * unsat g) with h | h
    · have hgap : gap ≤ unsat (iter amplify t g) := by omega
      omega
    · have hdouble : 2 ^ (t + 1) * unsat g ≤ 2 * unsat (iter amplify t g) := by
        rw [two_pow_succ_mul]; omega
      omega

/-- **Completeness** is preserved by iterating the amplification step. -/
