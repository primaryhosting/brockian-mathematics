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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Brockian.Weyl.WeylLawTarget

variable {α : Type u}

/-- `countingFunction lam L K` is the number of indices `n < K` whose eigenvalue `lam n`
lies at or below the threshold `L`.  For a discrete spectrum this stabilises as `K → ∞`
and its limiting value is the Weyl counting function `N(L) = #{n | lam n ≤ L}`. -/

theorem countingFunction_eq_self (K : Nat) (h : ∀ n : Nat, n < K → lam n ≤ L) :
    countingFunction lam L K = K := by
  induction K with
  | zero => rfl
  | succ n ih =>
    have hn : lam n ≤ L := h n (Nat.lt_succ_self n)
    have : countingFunction lam L n = n := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    simp [countingFunction, this, hn]

/-- Beyond a truncation level past which no eigenvalue lies below the threshold, the truncated
counts no longer change. -/
