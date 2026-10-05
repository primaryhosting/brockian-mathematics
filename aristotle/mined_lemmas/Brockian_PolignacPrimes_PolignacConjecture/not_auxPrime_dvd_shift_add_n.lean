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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` to precede any module docstring, so the required header
-- comment appears both at the very top of the file (as a plain comment) and, verbatim,
-- as the module docstring just above.

namespace Brockian.PolignacPrimes

open Nat

/-- `PolignacPair p n` says that `p` and `p + n` are *consecutive* primes:
both are prime and no number strictly between them is prime. -/

lemma not_auxPrime_dvd_shift_add_n {j : ℕ} (hj : j ∈ offsets n) :
    ¬ auxPrime n j ∣ (shift n + n) := by
  intro h
  have hd := auxPrime_dvd_shift_add n hj
  obtain ⟨hj1, hjn⟩ := (mem_offsets_iff n j).1 hj
  have hsub : auxPrime n j ∣ (n - j) := by
    have hrw : shift n + n = (shift n + j) + (n - j) := by omega
    rw [hrw] at h
    exact (Nat.dvd_add_right hd).1 h
  have hlt : n - j < auxPrime n j := lt_of_le_of_lt (Nat.sub_le _ _) (lt_auxPrime n j)
  have := Nat.le_of_dvd (by omega) hsub
  omega

/-- Admissibility of the pair of linear forms built from `modulus n` and `shift n`. -/
