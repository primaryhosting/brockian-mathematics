/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma ch_eq_one_iff (x : Fin 14) : ch x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hdvd : (14 : ℕ) ∣ x.val := (om_isPrimitiveRoot.pow_eq_one_iff_dvd x.val).1 h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt hdvd x.isLt)
  · rintro rfl; exact ch_zero

/-! ### Arithmetic helpers in `Fin 14` -/

