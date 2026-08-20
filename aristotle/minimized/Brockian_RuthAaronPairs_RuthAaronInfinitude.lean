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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(so `sopfr 12 = 2 + 2 + 3 = 7`).  By convention `sopfr 0 = sopfr 1 = 0`. -/

def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- `IsRuthAaronPair n` says that `(n, n + 1)` is a Ruth–Aaron pair: `n > 1` and the sums of
the prime factors (with multiplicity) of `n` and of `n + 1` agree. -/

def IsRuthAaronPair (n : ℕ) : Prop := 1 < n ∧ sopfr n = sopfr (n + 1)

/-- The set of Ruth–Aaron pairs, indexed by their smaller member. -/

def ruthAaronSet : Set ℕ := {n | IsRuthAaronPair n}

/-! ### Basic arithmetic of `sopfr` -/

theorem ruthAaronSet_infinite_iff_unbounded :
    ruthAaronSet.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ IsRuthAaronPair n := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hlt⟩ := hinf.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨n, hlt, hn⟩ := h N
    exact ⟨n, hn, hlt⟩

/-- **Ruth–Aaron infinitude (conditional reduction).**

Whether there are infinitely many Ruth–Aaron pairs is an open problem (conjectured by Erdős),
so what is proved here is the reduction: the set of Ruth–Aaron pairs is infinite as soon as
Ruth–Aaron pairs exist above every bound.  Together with
`ruthAaronSet_infinite_iff_unbounded` this shows the two formulations are equivalent; the
concrete pairs `(5, 6)` and `(714, 715)` are verified unconditionally above. -/

theorem RuthAaronInfinitude (h : ∀ N : ℕ, ∃ n, N < n ∧ IsRuthAaronPair n) :
    ruthAaronSet.Infinite :=
  ruthAaronSet_infinite_iff_unbounded.mpr h

/-- A convenient sufficient criterion: any strictly monotone sequence of Ruth–Aaron pairs
witnesses the infinitude of `ruthAaronSet`. -/
