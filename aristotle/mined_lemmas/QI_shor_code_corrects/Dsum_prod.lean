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

lemma Dsum_prod (r : Cfg) (u v : Bool) :
    Dsum r u v = ∏ b : Fin 3, Sblk (fun p => r (b, p)) u v := by
  set g : Fin 3 → (Fin 3 → Bool) → ℤ := fun b z =>
    (∏ p : Fin 3, if r (b, p) && z p then (-1 : ℤ) else 1) * bAmp u z * bAmp v z with hg
  have h1 : ∀ x : Cfg, zsI r x * wI u x * wI v x = ∏ b : Fin 3, g b (fun p => x (b, p)) := by
    intro x
    simp only [hg, Finset.prod_mul_distrib]
    congr 1
    congr 1
    · rw [zsI, Fintype.prod_prod_type]
  have h2 : (∑ x : Cfg, ∏ b : Fin 3, g b (fun p => x (b, p)))
      = ∑ y : Fin 3 → Fin 3 → Bool, ∏ b : Fin 3, g b (y b) :=
    Fintype.sum_equiv (Equiv.curry (Fin 3) (Fin 3) Bool) _ _ (fun _ => rfl)
  have h3 : (∏ b : Fin 3, Sblk (fun p => r (b, p)) u v)
      = ∑ y : Fin 3 → Fin 3 → Bool, ∏ b : Fin 3, g b (y b) := by
    have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3 → Bool))) g
    rw [Fintype.piFinset_univ] at this
    simpa [Sblk, hg] using this
  rw [Dsum, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => h1 x), h2, h3]

