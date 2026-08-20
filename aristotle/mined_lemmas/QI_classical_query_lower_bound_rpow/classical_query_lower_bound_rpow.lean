import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

theorem classical_query_lower_bound_rpow {n q : ℕ} (A : QueryAlg n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (q : ℝ) + 2 := by
  have h := classical_query_lower_bound A hA
  have h' : ((2:ℝ)) ^ (n : ℕ) ≤ ((q : ℝ) + 2) ^ 2 := by exact_mod_cast h
  have ha : (0:ℝ) ≤ (2:ℝ) ^ ((n : ℝ) / 2) := by positivity
  have hb : (0:ℝ) ≤ (q : ℝ) + 2 := by positivity
  have hsq : ((2:ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2:ℝ) ^ (n : ℕ) := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0), Real.rpow_natCast]
  nlinarith [h', ha, hb, hsq]

/-- **Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries.**

1. *(quantum, one query per round)* For every instance `f` with hidden shift `s`:
   * a single query produces a measurement outcome that is uniformly distributed
     on the hyperplane orthogonal to `s`;
   * the outcomes of `2 * n` independent rounds form a probability distribution,
     and the probability that they fail to determine `s` is at most `2 ^ (-n)`;
     so `2 * n = O(n)` queries suffice.
2. *(classical)* Every deterministic classical algorithm which always outputs the
   hidden shift using `q` queries satisfies `2 ^ (n / 2) ≤ q + 2`, i.e. it needs
   `Ω(2 ^ (n / 2))` queries. -/
