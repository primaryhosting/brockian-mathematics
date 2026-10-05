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

lemma gapTuple_upper {x : ℤ} (hx : x ∈ gapTuple) : x ≤ (1709 : ℤ) := by
  obtain ⟨n, hp, _, h2, rfl⟩ := mem_gapTuple_iff.mp hx
  have hne : n ≠ 1710 := by rintro rfl; exact absurd hp (by norm_num)
  have : n ≤ 1709 := by omega
  exact_mod_cast this

