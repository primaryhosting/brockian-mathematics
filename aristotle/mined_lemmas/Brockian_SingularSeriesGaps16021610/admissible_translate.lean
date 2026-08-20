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

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - 1/p)^{-|H|} (1 - ν_p(H)/p)` is nonzero at every prime. -/

theorem admissible_translate {H : Finset ℤ} (hH : Admissible H) (n : ℤ) :
    Admissible (H.image (fun h => h + n)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hH p hp
  refine ⟨r + (n : ZMod p), ?_⟩
  rintro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  simpa using fun hcon => hr h hh (by exact_mod_cast hcon)

/-- The gap pattern `0, 2, 6, 8, 12, 18, 20, 26`: an `8`-tuple of diameter `26`. -/
