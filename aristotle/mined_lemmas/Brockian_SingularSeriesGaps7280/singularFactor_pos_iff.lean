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
# Admissible tuples and positivity of the singular series

An `H : Finset ℕ` (thought of as a set of *gaps* / offsets of a prime constellation
`n + h`, `h ∈ H`) is **admissible** when, for every prime `p`, the reductions of `H`
modulo `p` do not cover all residue classes.  This is exactly the condition under which
the local factors of the Hardy–Littlewood singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p) (1 - 1/p)^(-|H|)` are all positive.

This file develops the basic theory and a general criterion producing admissible sets:
a set of size at most `m`, all of whose elements are coprime to `m !`, is admissible.
-/

open scoped BigOperators Nat

namespace Brockian

/-- The number of residue classes mod `p` occupied by `H`, i.e. `ν_H(p)`. -/

theorem singularFactor_pos_iff {H : Finset ℕ} {p : ℕ} (hp : p.Prime) :
    0 < singularFactor H p ↔ residueCount H p < p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbase : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    have h1 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast hp.one_lt
    linarith
  have hzpow : (0 : ℝ) < (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ)) := zpow_pos hbase _
  rw [singularFactor, mul_pos_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · have hdiv : (residueCount H p : ℝ) / p < 1 := by linarith
      rw [div_lt_one hp0] at hdiv
      exact_mod_cast hdiv
    · exact absurd h2 (not_lt.2 hzpow.le)
  · intro h
    refine Or.inl ⟨?_, hzpow⟩
    have hdiv : (residueCount H p : ℝ) / p < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast h
    linarith

/-- Admissibility is equivalent to positivity of every local factor of the singular
series. -/
