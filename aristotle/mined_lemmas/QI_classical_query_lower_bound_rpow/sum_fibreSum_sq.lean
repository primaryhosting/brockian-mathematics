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

lemma sum_fibreSum_sq (f : BV n → BV n) (y : BV n) :
    ∑ w : BV n, (fibreSum f y w) ^ 2 =
      ∑ x : BV n, ∑ x' : BV n, if f x = f x' then chi (ip x y) * chi (ip x' y) else 0 := by
  have inner : ∀ x x' : BV n,
      ∑ w : BV n, (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0)
        = if f x = f x' then chi (ip x y) * chi (ip x' y) else 0 := by
    intro x x'
    have hstep : ∀ w : BV n,
        (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0)
          = if f x = w then (if f x' = w then chi (ip x y) * chi (ip x' y) else 0) else 0 := by
      intro w; split <;> simp
    simp_rw [hstep]
    rw [Finset.sum_ite_eq Finset.univ (f x)
      (fun w => if f x' = w then chi (ip x y) * chi (ip x' y) else 0)]
    simp [eq_comm]
  calc ∑ w : BV n, (fibreSum f y w) ^ 2
      = ∑ w : BV n, ∑ x : BV n, ∑ x' : BV n,
          (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [sq, fibreSum, Finset.sum_mul_sum]
    _ = ∑ x : BV n, ∑ x' : BV n, ∑ w : BV n,
          (if f x = w then chi (ip x y) else 0) * (if f x' = w then chi (ip x' y) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => inner x x'

/-- For a Simon function, the fibre of `x` is the pair `{x, x + s}`. -/
