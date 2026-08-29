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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede any module doc comment, so the
-- required header block appears immediately after the single `import Mathlib` line.

namespace Brockian.LegendreConjecture

/-- `PrimeBetweenSquares n` states that there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2`. -/

theorem legendre_of_le_five_hundred (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 500) :
    PrimeBetweenSquares n := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨h2, hdiv⟩, hlo, hhi⟩ := legendreWitnesses_spec i (Finset.mem_range.mpr (by omega))
  set p := legendreWitnesses.getD i 0
  have hple : p < 501 ^ 2 := lt_of_lt_of_le hhi (Nat.pow_le_pow_left (by omega) 2)
  refine ⟨p, ?_, hlo, by omega⟩
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, fun m hm2 hms => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  have hm501 : m ≤ 501 := by nlinarith
  exact hdiv m (Finset.mem_Icc.mpr ⟨hm2, hm501⟩) hmm

end Brockian.LegendreConjecture

