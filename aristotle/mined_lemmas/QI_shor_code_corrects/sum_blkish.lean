import Mathlib
/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands in a
file, and `/-! ... -/` is a module doc-comment *command*, not a comment token.  The
required header block is therefore placed immediately after the single `import Mathlib`
line, which is the closest legal position to the top of the file.
-/

namespace QI

open Finset

noncomputable section

/-! ## The 9-qubit state space -/

/-- Qubit labels: three blocks of three qubits. -/
abbrev Qb := Fin 3 × Fin 3

/-- Computational basis labels for 9 qubits. -/
abbrev Cfg := Qb → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)`. -/
abbrev H := Cfg → ℂ

/-- Hermitian inner product, conjugate linear in the first argument. -/

lemma sum_blkish (f : Cfg → ℂ) :
    ∑ v : Cfg, (if blkish v then f v else 0) = ∑ c : Fin 3 → Bool, f (blk c) := by
  rw [← Finset.sum_filter]
  have himg : Finset.univ.filter blkish = Finset.image blk Finset.univ := by
    ext v
    constructor
    · intro h
      exact Finset.mem_image.2 ⟨bits v, Finset.mem_univ _, blk_bits (Finset.mem_filter.1 h).2⟩
    · intro h
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, blk_blkish c⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => blk_inj h)]

/-! ## The Shor code -/

/-- The sign `(-1)^(number of blocks set)`. -/
