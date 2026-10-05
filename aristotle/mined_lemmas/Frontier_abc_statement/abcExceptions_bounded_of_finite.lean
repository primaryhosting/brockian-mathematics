/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`. -/

theorem abcExceptions_bounded_of_finite (eps : ℝ) (h : (abcExceptions eps).Finite) :
    ∃ C : ℕ, ∀ t ∈ abcExceptions eps, t.2.2 ≤ C := by
  classical
  obtain ⟨s, hs⟩ := h.exists_finset
  refine ⟨(s.image (fun t : ℕ × ℕ × ℕ => t.2.2)).sup id, ?_⟩
  intro t ht
  exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ ((hs t).2 ht))

/-- **Reduction for the `abc` conjecture.**

The `abc` conjecture (for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a b c) ^ (1 + ε)`) is equivalent to the
statement that, for every `ε > 0`, the `c`-values of the exceptional triples are bounded.

(The `abc` conjecture itself is open; what is proved here is this equivalence, which reduces
a finiteness assertion to a uniform bound on `c`.) -/
