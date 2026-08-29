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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- (The header above is repeated here as a module docstring; a `/-!` block cannot precede
-- `import` in Lean 4.)
/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `n` is **`k`-hyperperfect** when `n = 1 + k * (σ n - n - 1)`, i.e. when
`k * σ n + 1 = (k + 1) * n + k`, where `σ n` is the sum of the divisors of `n`.
(The second, subtraction-free form is the one used here; `hyperperfect_iff_classical`
shows it agrees with the classical definition.) -/

theorem hyperperfect_iff_classical (k n : ℕ) :
    IsHyperperfect k n ↔
      1 < n ∧ (n : ℤ) = 1 + k * (((∑ d ∈ n.divisors, d : ℕ) : ℤ) - n - 1) := by
  unfold IsHyperperfect
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h2' : (k : ℤ) * ((∑ d ∈ n.divisors, d : ℕ) : ℤ) + 1 = ((k : ℤ) + 1) * n + k := by
      exact_mod_cast h2
    linarith [h2']
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : (k : ℤ) * ((∑ d ∈ n.divisors, d : ℕ) : ℤ) + 1 = ((k : ℤ) + 1) * n + k := by
      linarith [h2]
    exact_mod_cast this

/-- Sum of divisors of a product of two distinct primes. -/
