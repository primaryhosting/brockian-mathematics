/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header comment above uses `/- ... -/` rather than `/-! ... -/`: Lean requires all
-- `import` lines to precede any module docstring, so a `/-!` block cannot open the file.)

import Mathlib

open scoped BigOperators

/-!
# The 9-qubit Shor code corrects an arbitrary single-qubit error

The 9 qubits are grouped into three blocks of three, so a computational basis state of the
register is an element of `Cfg = Blk × Blk × Blk` with `Blk = Bool × Bool × Bool`, and a state
vector is a function `Cfg → ℂ` of amplitudes.

The logical codewords are

* `|0_L⟩ = (|000⟩ + |111⟩)^{⊗3} / (2√2)`,
* `|1_L⟩ = (|000⟩ - |111⟩)^{⊗3} / (2√2)`.

An arbitrary single-qubit error acting on qubit `j` of block `k` is given by an arbitrary
`2 × 2` complex matrix `A : Bool → Bool → ℂ` (no linearity, unitarity or normalization is
assumed).  The main theorem `QI.shor_code_corrects` establishes the Knill–Laflamme
error-correction conditions
`⟨c_a | A† B | c_b⟩ = δ_{a b} · α(A, B)`
for all pairs of single-qubit operators `A`, `B` placed at arbitrary (possibly different) qubits.
Note that `⟨c_a | A† B | c_b⟩ = ⟨A c_a , B c_b⟩`, which is the form used below.  Since every
single-qubit error operator is one of these and error channels are linear, these conditions are
exactly the statement that the code corrects an arbitrary single-qubit error.
-/

namespace QI

/-- Computational basis states of one 3-qubit block. -/
abbrev Blk := Bool × Bool × Bool

/-- Computational basis states of the 9-qubit register, grouped into three blocks. -/
abbrev Cfg := Blk × Blk × Blk

/-- Read qubit `j` of a block. -/

lemma ip_act_tri_blk (A B : Bool → Bool → ℂ) (k₁ j₁ k₂ j₂ : Fin 3) (a b : Bool) :
    ip (act A k₁ j₁ (tri (blk a) (blk a) (blk a))) (act B k₂ j₂ (tri (blk b) (blk b) (blk b)))
      = if a = b then ip (act A k₁ j₁ (tri (blk false) (blk false) (blk false)))
                        (act B k₂ j₂ (tri (blk false) (blk false) (blk false))) else 0 := by
  rcases fin3_cases k₁ with h₁ | h₁ | h₁ <;> rcases fin3_cases k₂ with h₂ | h₂ | h₂ <;>
    subst h₁ <;> subst h₂ <;>
    simp only [act_tri_zero, act_tri_one, act_tri_two, ip_tri] <;>
    cases a <;> cases b <;>
    simp [ipB_blk, ipB_actQ_left, ipB_actQ_right, ipB_actQ_both]

