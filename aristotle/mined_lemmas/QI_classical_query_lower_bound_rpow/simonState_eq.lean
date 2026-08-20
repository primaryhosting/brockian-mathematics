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

lemma simonState_eq (f : BV n → BV n) (y w : BV n) :
    simonState f (y, w) = (((2 : ℝ) ^ n)⁻¹ * fibreSum f y w : ℝ) := by
  have hcast : ((fibreSum f y w : ℝ) : ℂ)
      = ∑ x : BV n, (if f x = w then (chi (ip x y) : ℂ) else 0) := by
    rw [fibreSum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => by split <;> simp
  have key : ∀ x : BV n,
      (chi (ip x y) : ℂ) * (if w = f x then ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ)⁻¹ else 0)
        = ((Real.sqrt ((2:ℝ) ^ n) : ℝ) : ℂ)⁻¹ * (if f x = w then (chi (ip x y) : ℂ) else 0) := by
    intro x
    by_cases h : f x = w
    · simp [h, mul_comm]
    · simp [h, Ne.symm h]
  rw [Complex.ofReal_mul, hcast]
  simp only [simonState, hadamard1, unifState]
  rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.mul_sum, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, sqrt_two_pow_inv_sq n]

