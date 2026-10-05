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

lemma zeta_pow_n (hn : n ≠ 0) : zeta n ^ n = 1 := (isPrimitiveRoot_zeta hn).pow_eq_one

