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

theorem betrothedInfinitude_iff :
    {p : ℕ × ℕ | IsBetrothedPair p.1 p.2}.Infinite ↔ ∀ N : ℕ, ∃ m, N < m ∧ IsBetrothed m := by
  refine ⟨fun hinf N => ?_, BetrothedInfinitude⟩
  by_contra hc
  push_neg at hc
  have hsub : {p : ℕ × ℕ | IsBetrothedPair p.1 p.2} ⊆ Set.Iic N ×ˢ Set.Iic (N + N + 1) := by
    rintro ⟨m, n⟩ hmn
    have hm : IsBetrothed m := (isBetrothed_iff m).2 ⟨n, hmn⟩
    have hmN : m ≤ N := by by_contra h; exact absurd hm (hc m (by omega))
    have hn : IsBetrothed n := (isBetrothed_iff n).2 ⟨m, hmn.symm⟩
    have hnN : n ≤ N := by by_contra h; exact absurd hn (hc n (by omega))
    exact ⟨by simpa using hmN, by simp; omega⟩
  exact hinf (Set.Finite.subset ((Set.finite_Iic N).prod (Set.finite_Iic (N + N + 1))) hsub)

end Brockian.BetrothedNumbers

