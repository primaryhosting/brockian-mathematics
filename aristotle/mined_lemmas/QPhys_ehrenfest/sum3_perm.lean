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

private lemma sum3_perm {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k := by
  rw [sum3_inner f, Finset.sum_comm, sum3_inner fun k i j => f i j k]

