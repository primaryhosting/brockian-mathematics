/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

lemma singularFactor_pair_of_dvd {p : ℕ} (hp : p.Prime) {d : ℤ} (hd0 : d ≠ 0)
    (hd : (p : ℤ) ∣ d) :
    singularFactor p ({0, d} : Finset ℤ) = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  rw [singularFactor, nu_pair_of_dvd p hd, card_pair hd0]
  field_simp
  ring

/-- **Singular Series Gaps 13501360.**

For each gap `d` in the range `1350 ≤ d ≤ 1360`, the pair `{0, d}` is an admissible
Hardy–Littlewood tuple precisely when `d` is even; there are exactly six such admissible
gaps in this range, namely `1350, 1352, 1354, 1356, 1358, 1360`; and for each of them every
local factor of the singular series is strictly positive, hence so is every partial singular
series. -/
