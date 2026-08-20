import Brockian.CullenWoodall

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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Mathlib (as of this toolchain) contains no material on Cullen or Woodall numbers -- a search
for `Woodall` returns nothing -- so the notions below are developed from scratch.  The Mathlib
results actually used are `strictMono_nat_of_lt_succ`, `Nat.sub_lt_sub_right`,
`Set.infinite_of_not_bddAbove` and `Set.Infinite.exists_gt`.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/

theorem exists_large_index_of_infinite (h : WoodallPrimes.Infinite) :
    ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n) := by
  intro N
  obtain ⟨p, hp, hpN⟩ := h.exists_gt (2 ^ (N + 1) * (N + 1))
  obtain ⟨hprime, n, hn, rfl⟩ := hp
  refine ⟨n, ?_, hprime⟩
  by_contra hle
  push_neg at hle
  have hmono : woodall n ≤ woodall (N + 1) :=
    le_of_lt (woodall_lt_woodall hn (Nat.lt_succ_of_le hle))
  have hbd : woodall (N + 1) ≤ 2 ^ (N + 1) * (N + 1) := by
    simp only [woodall]
    calc (N + 1) * 2 ^ (N + 1) - 1 ≤ (N + 1) * 2 ^ (N + 1) := Nat.sub_le _ _
      _ = 2 ^ (N + 1) * (N + 1) := Nat.mul_comm _ _
  omega

/-- The reduction as an equivalence. -/
