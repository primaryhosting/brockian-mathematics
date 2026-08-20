/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- since Lean 4 requires `import` to be the first command in a file.)

import Mathlib

namespace QI

/-- The amplitude of the all-zeros outcome after the Deutsch–Jozsa circuit on an
`n`-qubit query register: after the Hadamard–oracle–Hadamard sandwich, the amplitude of
`|0…0⟩` is `2^(-n) * ∑_x (-1)^(f x)`. A single oracle query produces this amplitude. -/

theorem sum_eq_card_diff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1))
      = ({x | f x = false}.toFinset.card : ℝ) - ({x | f x = true}.toFinset.card : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = true)]
  have h1 : ∑ x ∈ Finset.univ.filter (fun x => f x = true), (if f x then (-1 : ℝ) else 1)
      = ∑ _x ∈ Finset.univ.filter (fun x => f x = true), (-1 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2]
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ (f x = true)), (if f x then (-1 : ℝ) else 1)
      = ∑ _x ∈ Finset.univ.filter (fun x => ¬ (f x = true)), (1 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2]
  rw [h1, h2, Finset.sum_const, Finset.sum_const]
  have e1 : Finset.univ.filter (fun x : Fin n → Bool => f x = true)
      = {x | f x = true}.toFinset := by
    ext x; simp
  have e2 : Finset.univ.filter (fun x : Fin n → Bool => ¬ (f x = true))
      = {x | f x = false}.toFinset := by
    ext x; simp
  rw [e1, e2]
  push_cast
  ring

/-- **Deutsch–Jozsa.** With a single oracle query, the all-zeros measurement outcome
distinguishes constant from balanced functions: for a constant `f` the amplitude of the
all-zeros outcome has modulus `1` (so the outcome occurs with probability `1`), while for a
balanced `f` the amplitude is `0` (so the outcome never occurs). -/
