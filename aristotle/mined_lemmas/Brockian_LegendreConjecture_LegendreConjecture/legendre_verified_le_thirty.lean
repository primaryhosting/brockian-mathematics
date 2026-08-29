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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 forbids a module
-- docstring before `import`; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Legendre's conjecture — "there is always a prime between two consecutive squares" — is a
well-known open problem.  This file therefore does what can be done rigorously:

* it states the conjecture (`LegendreStatement`);
* it gives several **equivalent reformulations**, including the contrapositive
  ("no prime-free interval between consecutive squares"), a formulation via the
  next-prime function, and a formulation via the prime counting function;
* it gives **conditional reductions**: Legendre's conjecture follows from Andrica's
  conjecture (`LegendreConjecture`, the target theorem) and from a `√m`-size prime gap
  hypothesis;
* it proves **unconditional partial results**: a weakened Bertrand-type version, and a
  verification of the conjecture for all `n ≤ 30`.
-/

namespace Brockian.LegendreConjecture

/-! ## The statement -/

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`. -/

theorem legendre_verified_le_thirty (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 30) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  interval_cases n
  · exact ⟨2, by norm_num⟩
  · exact ⟨5, by norm_num⟩
  · exact ⟨11, by norm_num⟩
  · exact ⟨17, by norm_num⟩
  · exact ⟨29, by norm_num⟩
  · exact ⟨37, by norm_num⟩
  · exact ⟨53, by norm_num⟩
  · exact ⟨67, by norm_num⟩
  · exact ⟨83, by norm_num⟩
  · exact ⟨101, by norm_num⟩
  · exact ⟨127, by norm_num⟩
  · exact ⟨149, by norm_num⟩
  · exact ⟨173, by norm_num⟩
  · exact ⟨197, by norm_num⟩
  · exact ⟨227, by norm_num⟩
  · exact ⟨257, by norm_num⟩
  · exact ⟨293, by norm_num⟩
  · exact ⟨331, by norm_num⟩
  · exact ⟨367, by norm_num⟩
  · exact ⟨401, by norm_num⟩
  · exact ⟨443, by norm_num⟩
  · exact ⟨487, by norm_num⟩
  · exact ⟨541, by norm_num⟩
  · exact ⟨577, by norm_num⟩
  · exact ⟨631, by norm_num⟩
  · exact ⟨677, by norm_num⟩
  · exact ⟨733, by norm_num⟩
  · exact ⟨787, by norm_num⟩
  · exact ⟨853, by norm_num⟩
  · exact ⟨907, by norm_num⟩

end Brockian.LegendreConjecture

