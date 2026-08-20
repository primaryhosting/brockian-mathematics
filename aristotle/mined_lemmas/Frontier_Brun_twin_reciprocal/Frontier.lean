import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

theorem Frontier.Brun_twin_reciprocal :
    Summable (fun p : {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} => (1 : ℝ) / (p.1 : ℝ)) := by
  have h : Summable (Brun.twinIndicator ∘
      (Subtype.val : {p : ℕ // Nat.Prime p ∧ Nat.Prime (p + 2)} → ℕ)) :=
    Brun.summable_twinIndicator'.comp_injective Subtype.val_injective
  refine h.congr (fun p => ?_)
  simp only [Function.comp_apply, Brun.twinIndicator, if_pos p.2]

import RequestProject.Brun.Defs

/-!
# Dyadic decomposition

Summability of `∑ 1/p` over twin primes follows from summability of
`m ↦ twinCount (2^m) / 2^m`.
-/

namespace Brun

open Finset

/-- `1/n` if `n, n+2` are both prime, and `0` otherwise. -/
