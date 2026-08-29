/-
/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- A finite set of integers `H` is *admissible* if for every prime `p` the reductions of the
elements of `H` modulo `p` omit at least one residue class.  Equivalently, the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` of the Hardy–Littlewood prime `k`-tuple conjecture
is nonzero. -/

theorem gapTuple_nu_lt (p : ℕ) (hp : p.Prime) : nu p gapTuple < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨r, hr⟩ := gapTuple_admissible p hp
  have hsub : gapTuple.image (fun h : ℤ => (h : ZMod p)) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    have : r ∈ gapTuple.image (fun h : ℤ => (h : ZMod p)) := by rw [hEq]; exact Finset.mem_univ r
    obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp this
    exact hr x hx hxr
  have := Finset.card_lt_card hsub
  rwa [Finset.card_univ, ZMod.card] at this

/-- **Singular Series Gaps 14501460.**  There is an admissible tuple of `214` integers whose
diameter `1458` lies in the gap range `[1450, 1460]`; consequently every local factor of its
singular series is positive.  (Admissibility of such a tuple is exactly the hypothesis needed for
the Hardy–Littlewood conjecture to predict infinitely many prime constellations with this gap.) -/
