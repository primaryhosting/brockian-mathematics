/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

theorem span_range_evec (n : ℕ) [NeZero n] :
    Submodule.span ℂ (Set.range (evec n)) = ⊤ :=
  (evec_linearIndependent n).span_eq_top_of_card_eq_finrank
    (by rw [Module.finrank_fintype_fun_eq_card])

/-- The isotypic planes exhaust the vertex space. -/
