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

theorem abcExceptions_finite_of_bounded (eps : ℝ) (C : ℕ)
    (h : ∀ t ∈ abcExceptions eps, t.2.2 ≤ C) : (abcExceptions eps).Finite := by
  apply Set.Finite.subset (Set.finite_Icc ((0 : ℕ), (0 : ℕ), (0 : ℕ)) (C, C, C))
  intro t ht
  have hC := h t ht
  obtain ⟨ha, hb, -, hsum, -⟩ := ht
  refine ⟨⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩, ?_, ?_, ?_⟩
  · show t.1 ≤ C
    omega
  · show t.2.1 ≤ C
    omega
  · show t.2.2 ≤ C
    omega

/-- If a set of `abc`-triples is finite, then the `c`-values occurring in it are bounded. -/
