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

lemma chi_ne_one [NeZero n] {t : Fin n} (ht : t ≠ 0) : chi n t ≠ 1 := by
  refine (isPrimitiveRoot_zeta (NeZero.ne n)).pow_ne_one_of_pos_of_lt ?_ t.isLt
  simpa [Fin.val_eq_zero_iff] using ht

