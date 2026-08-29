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

lemma qop_eq_sum (i : Idx) (M : Matrix Bool Bool ℂ) (f : St) :
    qop i M f = fun x => ∑ k : Bool × Bool, pcoef M k.1 k.2 * sq i k.1 k.2 f x := by
  funext x
  rw [qop]
  rw [Fintype.sum_prod_type]
  have step : ∀ pb : Bool,
      (∑ qb : Bool, pcoef M pb qb * sq i pb qb f x)
        = M (x i) (xor (x i) pb) * f (Function.update x i (xor (x i) pb)) := by
    intro pb
    have hM : M (x i) (xor (x i) pb)
        = ∑ qb : Bool, pcoef M pb qb * (if qb && xor (x i) pb then (-1 : ℂ) else 1) := by
      have := matrix_pauli_expansion M (x i) (xor (x i) pb)
      simpa [Bool.xor_left_comm] using this
    rw [hM, Finset.sum_mul]
    refine Finset.sum_congr rfl fun qb _ => ?_
    rw [sq_apply]
    ring
  rw [Finset.sum_congr rfl (fun pb (_ : pb ∈ Finset.univ) => step pb)]
  cases x i
  · simp
  · simp
    ring

/-! ## The key inner-product computations -/

/-- The integer core of the inner product `⟨w_u| Z^r |w_v⟩`. -/
