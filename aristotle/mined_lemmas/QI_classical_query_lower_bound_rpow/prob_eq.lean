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

theorem prob_eq {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) (y : BV n) :
    prob f y = if ip y s = 0 then 2 / 2 ^ n else 0 := by
  have hxs : ∀ x : BV n, x ≠ x + s := by
    intro x h
    apply hf.1
    have : x + 0 = x + s := by simpa using h
    exact (add_left_cancel this).symm
  have inner : ∀ x : BV n,
      (∑ x' : BV n, if f x = f x' then chi (ip x y) * chi (ip x' y) else 0)
        = 1 + chi (ip s y) := by
    intro x
    rw [← Finset.sum_filter, filter_fibre hf x,
      Finset.sum_pair (hxs x), chi_mul_self]
    rw [ip_add_left, chi_add, ← mul_assoc, chi_mul_self, one_mul]
  have hsum : ∑ w : BV n, (fibreSum f y w) ^ 2 = 2 ^ n * (1 + chi (ip s y)) := by
    rw [sum_fibreSum_sq]
    simp_rw [inner]
    rw [Finset.sum_const, Finset.card_univ, card_bv, nsmul_eq_mul]
    push_cast
    ring
  rw [prob_eq_sum_sq, hsum]
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rcases zmod_two_cases (ip y s) with h | h
  · rw [if_pos h, ip_comm s y, h, show chi 0 = 1 from by rw [chi, if_pos rfl]]
    field_simp
    ring
  · rw [if_neg (by rw [h]; decide), ip_comm s y, h,
      show chi 1 = -1 from by rw [chi, if_neg (by decide)]]
    ring

end QI

import Mathlib

/-!
# Simon's problem: basic definitions

We work with the `𝔽₂`-vector space `BV n = Fin n → ZMod 2` of `n`-bit strings,
equipped with the standard bilinear form `ip x y = ∑ i, x i * y i`.

A function `f : BV n → BV n` *satisfies the Simon promise with hidden shift `s`*
(`IsSimon f s`) when `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`; i.e. `f` is
two-to-one and its fibres are the cosets of the subgroup `{0, s}`.
-/

namespace QI

/-- `n`-bit strings, viewed as a vector space over `𝔽₂`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The standard bilinear form on `BV n`. -/
