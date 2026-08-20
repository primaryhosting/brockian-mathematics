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

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when for every prime `p` the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem intCast_zmod_two_eq_zero_of_even {d : ℤ} (hd : Even d) : ((d : ℤ) : ZMod 2) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast hd.two_dvd

/-- Every even gap gives an admissible pair `{0, d}`. -/
