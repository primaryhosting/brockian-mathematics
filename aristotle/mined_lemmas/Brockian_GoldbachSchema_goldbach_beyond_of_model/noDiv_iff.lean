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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-! ## The statements -/

/-- `GoldbachPair n` : `n` is a sum of two primes. -/

theorem noDiv_iff (n : ℕ) : ∀ k : ℕ, noDiv n k = true ↔ ∀ m : ℕ, 2 ≤ m → m ≤ k → ¬ (m ∣ n) := by
  intro k
  induction k with
  | zero => simp [noDiv]; omega
  | succ k ih =>
    match k with
    | 0 => simp [noDiv]; omega
    | (j + 1) =>
      simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq, ih]
      constructor
      · rintro ⟨h1, h2⟩ m hm hmk
        rcases Nat.lt_or_ge m (j + 2) with h | h
        · exact h2 m hm (by omega)
        · have hmj : m = j + 2 := by omega
          subst hmj
          exact fun hd => h1 (Nat.mod_eq_zero_of_dvd hd)
      · intro h
        refine ⟨?_, fun m hm hmk => h m hm (by omega)⟩
        exact fun hc => h (j + 2) (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hc)

/-- Trial-division primality certificate: `k` is a trial-division bound, valid whenever
`n < (k+1)^2`. -/
