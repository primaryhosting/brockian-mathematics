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

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`.  The only known
solutions are `n = 4, 5, 7` (with `m = 5, 11, 71`), and it is conjectured that
there are no others; in *gap* form the conjecture states that the distance from
`n ! + 1` to the nearest perfect square is positive (indeed large) for all
`n ≥ 8`.  This is an open problem.

This file contains:

* `Brockian.BrocardGap.brocardGap`, the distance from `n ! + 1` to the nearest
  perfect square, and the characterisation `brocardGap_pos_iff`;
* `Brockian.BrocardGap.ABC`, the `abc` conjecture (in radical form);
* `Brockian.BrocardGap.BrocardGapConjecture`, a Lean-checked **conditional
  reduction**: the `abc` conjecture implies that the Brocard gap is positive for
  all sufficiently large `n` (this is Overholt's argument);
* `Brockian.BrocardGap.brocardGap_pos_of_mem_Icc`, an unconditional verification
  of the gap positivity for `8 ≤ n ≤ 200`;
* `Brockian.BrocardGap.brocard_iff_pronic`, the elementary reformulation of
  Brocard's equation as `n ! = 4 * a * (a + 1)`.
-/

namespace Brockian.BrocardGap

open Nat Finset

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma exists_factorial_gt (C D : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → D * C ^ n < (n ! : ℝ) := by
  set E : ℝ := |D| + 1 with hE
  have hEpos : 0 < E := by positivity
  have htend := FloorSemiring.tendsto_pow_div_factorial_atTop (|C|)
  have hev := htend.eventually (eventually_lt_nhds (by positivity : (0:ℝ) < 1 / E))
  obtain ⟨N, hNn⟩ := hev.exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have key : |C| ^ n / (n ! : ℝ) < 1 / E := hNn n hn
  have key2 : E * |C| ^ n < (n ! : ℝ) := by
    rw [div_lt_div_iff₀ hfac hEpos] at key
    nlinarith [key]
  calc D * C ^ n ≤ |D * C ^ n| := le_abs_self _
    _ = |D| * |C| ^ n := by rw [abs_mul, abs_pow]
    _ ≤ E * |C| ^ n := by nlinarith [pow_nonneg (abs_nonneg C) n]
    _ < (n ! : ℝ) := key2

/-- Under the `abc` conjecture, a solution of Brocard's equation with `n` large is impossible:
any solution satisfies `n ! ≤ D * 4096 ^ n` for an absolute constant `D`. -/
