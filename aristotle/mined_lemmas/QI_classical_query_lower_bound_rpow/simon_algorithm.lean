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

theorem simon_algorithm :
    (∀ (n : ℕ) (f : BV n → BV n) (s : BV n), IsSimon f s →
        (∀ y : BV n, prob f y = if ip y s = 0 then 2 / 2 ^ n else 0) ∧
        (∑ Y : Fin (2 * n) → BV n, ∏ i, prob f (Y i)) = 1 ∧
        failProb f s (2 * n) ≤ 1 / 2 ^ n) ∧
    (∀ (n q : ℕ) (A : QueryAlg n),
        (∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) →
        (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (q : ℝ) + 2) := by
  refine ⟨fun n f s hf =>
      ⟨fun y => prob_eq hf y, sum_prod_prob_eq_one hf (2 * n), quantum_simon_success hf⟩,
    fun _ _ A hA => classical_query_lower_bound_rpow A hA⟩

end QI

import RequestProject.Simon.Basic

/-!
# Simon's problem: the quantum subroutine

One round of Simon's algorithm uses a *single* query to the oracle for `f`:

* prepare `2^(-n/2) ∑ₓ |x⟩|0⟩` and query the oracle, giving
  `unifState f = 2^(-n/2) ∑ₓ |x⟩|f x⟩`;
* apply the Hadamard transform to the first register, giving `simonState f`;
* measure the first register.

The main result `QI.prob_eq` computes the resulting distribution: the outcome is
uniformly distributed on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to the
hidden shift `s`.
-/

namespace QI

variable {n : ℕ}

/-- The state `2^(-n/2) ∑ₓ |x⟩|f x⟩` obtained from `|0⟩|0⟩` by Hadamards on the
first register followed by one oracle query. -/
