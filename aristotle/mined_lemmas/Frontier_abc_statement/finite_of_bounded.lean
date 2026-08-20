import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede all other commands, including module docstrings.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma finite_of_bounded (M : ℕ) :
    {t : ℕ × ℕ × ℕ | t.1 + t.2.1 = t.2.2 ∧ t.2.2 ≤ M}.Finite := by
  apply Set.Finite.subset
    (Finset.finite_toSet ((Finset.range (M + 1)) ×ˢ (Finset.range (M + 1)) ×ˢ
      (Finset.range (M + 1))))
  rintro ⟨a, b, c⟩ ⟨hsum, hle⟩
  dsimp only at hsum hle
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  refine ⟨by omega, by omega, by omega⟩

/-- `rad 72 = 6`. -/
