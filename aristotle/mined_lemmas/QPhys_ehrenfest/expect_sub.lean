import Mathlib
/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the mandated header comment is placed immediately after the single `import Mathlib`
line; its text is reproduced verbatim.
-/

namespace QPhys

open Finset

/-- The expectation value `⟨ψ| M |ψ⟩ = ∑ i j, conj (ψ i) * M i j * ψ j` of a (matrix)
observable `M` in the state `ψ`. -/

lemma expect_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect (M - N) v = expect M v - expect N v := by
  simp only [expect, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Expectation value of a product, written as a triple sum. -/
