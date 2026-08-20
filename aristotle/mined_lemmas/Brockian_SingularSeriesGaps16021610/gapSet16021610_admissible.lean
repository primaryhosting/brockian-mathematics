/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The gap pattern `(0, 1602, 1610)`, i.e. the triple of integer shifts
`{0, 1602, 1610}` (gaps `1602` and `1610` from the base point). -/

theorem gapSet16021610_admissible :
    ∀ p : ℕ, p.Prime → ∃ r : ℤ, ∀ h ∈ gapSet16021610, ¬ ((p : ℤ) ∣ (h - r)) := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r0, hr0⟩ := SingularSeriesGaps16021610 p hp
  refine ⟨(r0.val : ℤ), ?_⟩
  intro h hh hdvd
  have hcast : ((h - (r0.val : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  have hEq : (h : ZMod p) = r0 := by
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  exact hr0 h hh hEq

/-- `nuP p` is `ν_p(H)`, the number of residue classes mod `p` occupied by the
gap range `H = {0, 1602, 1610}`. -/
