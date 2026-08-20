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

lemma exists_ip_zero_ip_one {s t : BV n} (ht : t ≠ 0) (hst : t ≠ s) :
    ∃ y : BV n, ip y s = 0 ∧ ip y t = 1 := by
  have hne : ∃ i, s i ≠ t i := by
    by_contra h
    push_neg at h
    exact hst (funext fun i => (h i).symm)
  obtain ⟨i, hi⟩ := hne
  rcases zmod_two_cases (s i) with h0 | h1
  · -- s i = 0, hence t i = 1
    have hti : t i = 1 := by
      rcases zmod_two_cases (t i) with h | h
      · exact absurd (h0.trans h.symm) hi
      · exact h
    exact ⟨e i, by rw [ip_e_left, h0], by rw [ip_e_left, hti]⟩
  · -- s i = 1, hence t i = 0
    have hti : t i = 0 := by
      rcases zmod_two_cases (t i) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hi
    obtain ⟨j, hj⟩ := exists_ne_zero_coord ht
    refine ⟨e j + s j • e i, ?_, ?_⟩
    · rw [ip_add_left, ip_e_left]
      have : ip (s j • e i) s = s j * s i := by
        simp [ip, e, Finset.sum_ite_eq' Finset.univ i]
      rw [this, h1, mul_one, zmod_two_add_self]
    · rw [ip_add_left, ip_e_left]
      have : ip (s j • e i) t = s j * t i := by
        simp [ip, e, Finset.sum_ite_eq' Finset.univ i]
      rw [this, hti, mul_zero, add_zero, hj]

end

end QI

import RequestProject.Simon.Quantum

/-!
# Simon's problem: `O(n)` quantum queries suffice

Each run of the quantum subroutine costs one query and returns a uniformly
random element of the hyperplane `orth s = {y | ⟪y, s⟫ = 0}` (`QI.prob_eq`).

After `m` runs, the classical post-processing solves the linear system
`⟪y i, t⟫ = 0` and outputs the unique nonzero solution, which succeeds exactly
when the sample tuple `Y` *determines* `s` (`QI.Determines`).  The main estimate
`QI.failProb_le` bounds the probability of failure by `2 ^ n / 2 ^ m`; with
`m = 2 * n` queries the failure probability is at most `2 ^ (-n)`
(`QI.quantum_simon_success`).
-/

namespace QI

variable {n : ℕ}

/-- The hyperplane orthogonal to `s`. -/
