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
import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Legendre's conjecture — that for every `n ≥ 1` there is a prime strictly between `n ^ 2` and
`(n + 1) ^ 2` — is a well-known open problem.  This file therefore contains:

* `Brockian.LegendreConjecture.LegendreStatement`, the formal statement of the conjecture;
* several *equivalent* reformulations (contrapositive form, a counting form using
  `Finset` cardinalities, and a form using the prime counting function `π`);
* `Brockian.LegendreConjecture.LegendreConjecture`, a Lean-checked **conditional reduction**:
  Legendre's conjecture follows from the (also open, but formally weaker-looking) statement
  that every interval `(m, m + √m]` contains a prime;
* `Brockian.LegendreConjecture.legendre_of_le_hundred`, an unconditional verification of the
  conjecture for all `1 ≤ n ≤ 100`.
-/

namespace Brockian.LegendreConjecture

open Finset

/-- The statement of Legendre's conjecture: for every `n ≥ 1` there is a prime `p` with
`n ^ 2 < p < (n + 1) ^ 2`. -/

theorem legendre_of_le_hundred (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 100) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  interval_cases n
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨53, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨67, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨83, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨127, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨149, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨173, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨197, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨227, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨257, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨293, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨331, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨367, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨401, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨443, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨487, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨541, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨577, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨631, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨677, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨733, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨787, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨853, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨907, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨967, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1031, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1091, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1163, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1297, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1373, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1447, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1523, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1601, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1693, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1777, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1861, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1949, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2027, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2129, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2213, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2309, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2411, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2503, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2609, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2707, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2819, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2917, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3037, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3137, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3251, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3371, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3491, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3607, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3727, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3847, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3989, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4099, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4357, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4493, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4637, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4783, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4903, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5051, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5189, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5333, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5477, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5639, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5779, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5939, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6089, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6247, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6421, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6563, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6733, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6899, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7057, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7411, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7573, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7753, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7927, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8287, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8467, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8663, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8837, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9029, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9221, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9413, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9613, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9803, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10007, by norm_num, by norm_num, by norm_num⟩

/-- Unconditional weakening of Legendre's conjecture, from Bertrand's postulate: for every
`n ≥ 1` there is a prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
