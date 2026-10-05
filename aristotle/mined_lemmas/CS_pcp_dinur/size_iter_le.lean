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

theorem size_iter_le (size : G → Nat) (amplify : G → G) (C : Nat)
    (hsize : ∀ g, size (amplify g) ≤ C * size g) :
    ∀ (t : Nat) (g : G), size (iter amplify t g) ≤ C ^ t * size g := by
  intro t
  induction t with
  | zero => intro g; simp
  | succ t ih =>
    intro g
    rw [iter_succ]
    calc size (amplify (iter amplify t g)) ≤ C * size (iter amplify t g) := hsize _
      _ ≤ C * (C ^ t * size g) := Nat.mul_le_mul_left _ (ih g)
      _ = C ^ (t + 1) * size g := by
          rw [Nat.pow_succ, Nat.mul_comm (C ^ t) C, Nat.mul_assoc]

/--
**Dinur's gap amplification yields the PCP theorem** (abstract combinatorial form).

`G` is a type of constraint systems.  Each `g : G` has a `size` (number of constraints)
and an *unsatisfiability value* — the fraction of constraints violated by a best
assignment — which is recorded here in scaled integer form: the true value is
`unsat g / D` for a fixed denominator `D ≥ 1`.  Likewise the target constant gap is
`gap / D`.

The hypotheses are exactly the properties of one round of Dinur's transformation:

* `hsize`     : the size grows by at most a constant factor `C`;
* `hcomplete` : perfect completeness is preserved (satisfiable stays satisfiable);
* `hamplify`  : the unsat value at least doubles, until the constant `gap / D` is reached;
* `hsound`    : an unsatisfiable system violates at least one constraint, i.e. its unsat
                value `unsat g / D` is at least `1 / size g`.

Conclusion: for every size bound `n ≥ 1` there is a round count `t` that is only
*logarithmic* in `n` (witnessed by `2 ^ t ≤ 2 * (gap * n) + 1`), so that the total size
blow-up `C ^ t` is polynomial in `n`, and after `t` rounds every system of size at most
`n` is transformed into one that

* is still perfectly satisfiable if the original was, and
* otherwise has unsat value at least the *constant* `gap / D`.

This constant-gap, polynomial-size reduction is precisely the content of the PCP
