import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the header
comment above is placed immediately after the single `import Mathlib` line.)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma chi_pow_n [NeZero n] (t : Fin n) : (chi n t) ^ n = 1 := by
  rw [chi, ← pow_mul, mul_comm, pow_mul, zeta_pow_n (NeZero.ne n), one_pow]

/-- Orthogonality relation for the characters `chi n`. -/
