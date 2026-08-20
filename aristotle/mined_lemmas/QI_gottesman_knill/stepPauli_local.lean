/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

lemma stepPauli_local {n : ℕ} (g : Gate n) (P : Pauli n) :
    ((Finset.univ.filter
      (fun k => (stepPauli g P).xs k ≠ P.xs k ∨ (stepPauli g P).zs k ≠ P.zs k)).card) ≤ 2 := by
  have key : ∀ i j : Fin n,
      (Finset.univ.filter
        (fun k => (stepPauli g P).xs k ≠ P.xs k ∨ (stepPauli g P).zs k ≠ P.zs k))
        ⊆ ({i, j} : Finset (Fin n)) →
      ((Finset.univ.filter
        (fun k => (stepPauli g P).xs k ≠ P.xs k ∨ (stepPauli g P).zs k ≠ P.zs k)).card) ≤ 2 := by
    intro i j hsub
    refine le_trans (Finset.card_le_card hsub) ?_
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  cases g with
  | H i =>
    refine key i i ?_
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    rcases hk with hk | hk <;>
      exact hk (by simp [stepPauli, Function.update_of_ne hne.1])
  | S i =>
    refine key i i ?_
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    rcases hk with hk | hk
    · exact hk (by simp [stepPauli])
    · exact hk (by simp [stepPauli, Function.update_of_ne hne.1])
  | CX i j h =>
    refine key j i ?_
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push_neg at hne
    rcases hk with hk | hk
    · exact hk (by simp [stepPauli, Function.update_of_ne hne.1])
    · exact hk (by simp [stepPauli, Function.update_of_ne hne.2])

/-! ## Measurement statistics -/

/-- The probability of observing `0` on qubit `k` when measuring the output of a stabilizer
circuit in the computational basis is determined by a single classically simulated
Pauli expectation value. -/
