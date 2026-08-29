/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring before the `import` commands.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

The state space of `7` qubits is modelled as the space of complex-valued functions on
`Vec := Fin 7 → ZMod 2`, the set of the `2^7` computational basis labels, with the
standard hermitian inner product `ip`.  Linear operators are `Matrix Vec Vec ℂ` acting
by `Matrix.mulVec`.
-/

/-- Computational basis labels for 7 qubits. -/
abbrev Vec := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form on `Vec`. -/

lemma oneQubitOp_mulVec {i : Fin 7} {M : Matrix Vec Vec ℂ} (h : OneQubitOp i M) :
    ∃ cc : ZMod 2 → ZMod 2 → ℂ, ∀ f : Vec → ℂ,
      M.mulVec f = ∑ s : ZMod 2, ∑ t : ZMod 2, cc s t • (pauli (unit i s) (unit i t)).mulVec f := by
  obtain ⟨m, hm⟩ := h
  refine ⟨ccOf m, fun f => ?_⟩
  funext x
  have hentry : ∀ y : Vec, M x y
      = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t * pauli (unit i s) (unit i t) x y := by
    intro y
    rw [hm x y]
    exact oneQubit_entry i m x y
  have hRHS : (∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t • (pauli (unit i s) (unit i t)).mulVec f) x
      = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t * ((pauli (unit i s) (unit i t)).mulVec f x) := by
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hRHS]
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ y : Vec, M x y * f y
      = ∑ y : Vec, (∑ s : ZMod 2, ∑ t : ZMod 2,
          ccOf m s t * pauli (unit i s) (unit i t) x y) * f y :=
        Finset.sum_congr rfl (fun y _ => by rw [hentry y])
    _ = ∑ y : Vec, ∑ s : ZMod 2, ∑ t : ZMod 2,
          ccOf m s t * pauli (unit i s) (unit i t) x y * f y := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_mul])
    _ = ∑ s : ZMod 2, ∑ t : ZMod 2, ∑ y : Vec,
          ccOf m s t * pauli (unit i s) (unit i t) x y * f y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_comm])
    _ = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t
          * ∑ y : Vec, pauli (unit i s) (unit i t) x y * f y := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by ring)

/-! ## Main theorem -/

/-- Single-qubit Pauli operators are indeed single-qubit operators. -/
