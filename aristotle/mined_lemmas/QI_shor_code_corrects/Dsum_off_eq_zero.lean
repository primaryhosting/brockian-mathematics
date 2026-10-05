/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above
-- is written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/-! ## Setup

The nine qubits of the Shor code are indexed by `Idx = Fin 3 × Fin 3`: the first
component is the block (of the outer phase-flip code), the second the position
inside the block (the inner bit-flip repetition code).

A computational basis state is a configuration `Cfg = Idx → Bool`, and a state
vector is a function `St = Cfg → ℂ` giving the amplitude of each basis state.
-/

/-- Index set of the nine qubits: `(block, position)`. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- A computational basis label for the nine qubits. -/
abbrev Cfg : Type := Idx → Bool

/-- A state vector of the nine-qubit register. -/
abbrev St : Type := Cfg → ℂ

/-- The standard hermitian inner product on the nine-qubit state space,
antilinear in the first argument. -/

lemma Dsum_off_eq_zero {r : Cfg} {i j : Idx} (hsupp : ∀ k, r k = true → k = i ∨ k = j)
    {u v : Bool} (huv : u ≠ v) : Dsum r u v = 0 := by
  obtain ⟨b, hbi, hbj⟩ := exists_free_block i j
  have hzero : (fun p => r (b, p)) = (fun _ : Fin 3 => false) := by
    funext p
    by_contra hne
    rcases hsupp (b, p) (by simpa using hne) with h | h
    · exact hbi (congrArg Prod.fst h)
    · exact hbj (congrArg Prod.fst h)
  rw [Dsum_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  rw [hzero]
  exact Sblk_zero_off u v huv

