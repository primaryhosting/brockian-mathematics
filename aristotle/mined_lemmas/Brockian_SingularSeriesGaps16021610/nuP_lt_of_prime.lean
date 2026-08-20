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

theorem nuP_lt_of_prime (p : ℕ) (hp : p.Prime) : nuP p < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r, hr⟩ := SingularSeriesGaps16021610 p hp
  have hrmem : r ∉ gapSet16021610.image (fun h : ℤ => (h : ZMod p)) := by
    intro hmem
    obtain ⟨h, hh, hcast⟩ := Finset.mem_image.mp hmem
    exact hr h hh hcast
  have hss : gapSet16021610.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    exact hrmem (hEq ▸ Finset.mem_univ r)
  have := Finset.card_lt_card hss
  rwa [Finset.card_univ, ZMod.card] at this

/-- The local factor `1 - ν_p(H)/p` of the singular series of the gap range
`{0, 1602, 1610}` is strictly positive at every prime `p`; hence no factor of the
singular series vanishes. -/
