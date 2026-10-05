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

lemma mem_gapTuple_iff {x : ℤ} :
    x ∈ gapTuple ↔ ∃ n : ℕ, n.Prime ∧ 251 ≤ n ∧ n < 1711 ∧ (n : ℤ) = x := by
  simp only [gapTuple, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨n, ⟨⟨h1, h2⟩, hp⟩, rfl⟩; exact ⟨n, hp, h1, h2, rfl⟩
  · rintro ⟨n, hp, h1, h2, rfl⟩; exact ⟨n, ⟨⟨h1, h2⟩, hp⟩, rfl⟩

