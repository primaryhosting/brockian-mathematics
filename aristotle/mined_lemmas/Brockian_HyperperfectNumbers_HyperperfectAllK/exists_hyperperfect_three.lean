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

theorem exists_hyperperfect_three : ∃ n : ℕ, IsHyperperfect 3 n :=
  HyperperfectAllK 3 (by norm_num)
    (Or.inr ⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩)

/-- `301` is `6`-hyperperfect. -/
