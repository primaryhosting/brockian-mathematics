/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace CS

/-! ## Boolean strings, probabilities and majority votes -/

/-- Boolean strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The probability that the test `T` accepts a uniformly random string of length `k`. -/

theorem maj_comp_eq_true {k l : ℕ} (T : Bits k → Bool) (G : Bits l → Bits k)
    (h : |prob T - prob (fun s => T (G s))| < 1 / 6) (hT : 2 / 3 ≤ prob T) :
    maj (fun s => T (G s)) = true := by
  rw [abs_sub_lt_iff] at h
  have h1 := h.1
  simp only [maj, decide_eq_true_eq]
  linarith

