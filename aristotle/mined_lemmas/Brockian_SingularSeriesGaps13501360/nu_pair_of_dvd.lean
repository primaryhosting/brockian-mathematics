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

lemma nu_pair_of_dvd (p : ℕ) {d : ℤ} (hd : (p : ℤ) ∣ d) : nu p ({0, d} : Finset ℤ) = 1 := by
  have h : ((d : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).2 hd
  simp [nu, Finset.image_insert, h]

/-- If `p` does not divide `d` then the pair `{0, d}` occupies two classes mod `p`. -/
