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

lemma zero_missed_of_small {p : ℕ} (hp : p.Prime) (hle : p ≤ 250) :
    ∀ h ∈ gapTuple, (h : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro x hx
  obtain ⟨n, hn, h1, _, rfl⟩ := mem_gapTuple_iff.mp hx
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := (Nat.prime_dvd_prime_iff_eq hp hn).mp hdvd
  omega

