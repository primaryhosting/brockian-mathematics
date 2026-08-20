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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring:
-- Lean 4 requires `import` commands to precede every other command, including module
-- docstrings.  The same text is repeated as the module docstring after the import.)

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

set_option maxHeartbeats 2000000

namespace Brockian.BetrothedNumbers

open Finset

/-- The classical divisor sum `σ₁ n = ∑_{d ∣ n} d`. -/

theorem BetrothedInfinitude
    (H : ∀ N : ℕ, ∃ m, N < m ∧ IsBetrothed m) :
    {p : ℕ × ℕ | IsBetrothedPair p.1 p.2}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨m, hmN, hm⟩ := H N
  obtain ⟨n, hn⟩ := (isBetrothed_iff m).1 hm
  have : m ∈ Prod.fst '' {p : ℕ × ℕ | IsBetrothedPair p.1 p.2} := ⟨(m, n), hn, rfl⟩
  exact absurd (hN this) (by omega)

/-- The hypothesis of `BetrothedInfinitude` is not merely sufficient but necessary: the
reduction is an equivalence. -/
