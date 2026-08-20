/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
Mathlib lemmas doing the real work here: `Finset.card_image_le` (bounds the local density
`ν_H(p)` by `|H|`), `ZMod.natCast_eq_zero_iff` (evens vanish mod `2`), and
`Finset.prod_pos` (positivity of the truncated Euler product).
-/

namespace Brockian

/-- The local density `ν_H(p)`: the number of residue classes modulo `p` occupied by the
shift set `H`.  This is the quantity appearing in each Euler factor of the Hardy–Littlewood
singular series of the tuple `H`. -/

lemma euler_factor_pos {H : Finset ℕ} (hH : Admissible H) {p : ℕ} (hp : p.Prime) :
    0 < (1 - (localDensity H p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ H.card := by
  have hp2 : (2 : ℕ) ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnum : 0 < 1 - (localDensity H p : ℝ) / (p : ℝ) := by
    have hlt : (localDensity H p : ℝ) < (p : ℝ) := by exact_mod_cast hH p hp
    have := (div_lt_one hp0).mpr hlt
    linarith
  have hden : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  exact div_pos hnum (pow_pos hden _)

/-- The truncated singular series of an admissible tuple is strictly positive; in particular
it never vanishes, which is the local obstruction-free condition in the prime `k`-tuples
conjecture. -/
