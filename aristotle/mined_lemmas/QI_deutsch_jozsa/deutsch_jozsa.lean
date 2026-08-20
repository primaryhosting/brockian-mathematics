import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Bool) → Bool)
    (h : IsConstant f ∨ IsBalanced f) :
    (IsConstant f ↔ |amp f (zeroStr n)| = 1) ∧ (IsBalanced f ↔ amp f (zeroStr n) = 0) := by
  refine ⟨⟨abs_amp_eq_one_of_constant f, ?_⟩,
    ⟨amp_eq_zero_of_balanced f, balanced_of_amp_eq_zero f⟩⟩
  intro habs
  rcases h with hc | hb
  · exact hc
  · rw [amp_eq_zero_of_balanced f hb] at habs
    norm_num at habs

/-! ### Unitarity: the numbers `amp f y` really are the amplitudes of a quantum state -/

/-- Orthogonality of the rows of the `n`-fold Hadamard transform. -/
