/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem zeta_inv_three : (zeta ^ 3)⁻¹ = zeta ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact zeta_pow_seven)

/-- Elementary symmetric function of degree one of the three nontrivial eigenvalues. -/
