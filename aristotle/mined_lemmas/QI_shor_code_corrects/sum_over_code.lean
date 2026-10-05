/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

lemma sum_over_code (f : Bits → ℂ) (hf : ∀ b, ¬ isCode b → f b = 0) :
    ∑ b : Bits, f b = ∑ c : Fin 3 → ZMod 2, f (rep c) := by
  have himg : ∑ b ∈ Finset.univ.image rep, f b = ∑ c : Fin 3 → ZMod 2, f (rep c) :=
    Finset.sum_image (fun x _ y _ h => rep_injective h)
  rw [← himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro b _ hb
  refine hf b ?_
  intro hcode
  exact hb (Finset.mem_image.2 ⟨blk b, Finset.mem_univ _, rep_blk hcode⟩)

/-- The normalisation constant `1 / (2√2)` of the Shor codewords. -/
