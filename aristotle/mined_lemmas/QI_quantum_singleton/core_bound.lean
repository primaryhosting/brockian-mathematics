/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

An `[[n, k, d]]_q` quantum error-correcting code is a subspace `C` of the `n`-qudit space
`(ℂ^q)^{⊗ n}`, here modelled as `EuclideanSpace ℂ (Fin n → Fin q)` (functions on the set of
classical configurations), of dimension `q ^ k`, such that every set `A` of at most `d - 1`
sites is *correctable*, i.e. satisfies the Knill–Laflamme condition
`P E P = λ(E) P` for all operators `E` supported on `A` (equivalently, for all matrix units,
which is the form used below).

The main result `QI.quantum_singleton` is the quantum Singleton bound `n - k ≥ 2 (d - 1)`.

The proof is the rank version of the standard entropic argument: for two disjoint correctable
sets `A`, `B`, writing `K` for the dimension of the code, `r_A`, `r_B` for the ranks of the
reduced density matrices on `A`, `B` and `γ` for the configuration space of the remaining
sites, one has `K * r_A ≤ |γ| * r_B` and `K * r_B ≤ |γ| * r_A`, whence `K ≤ |γ|`.
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

open scoped ComplexConjugate
open Module (finrank)

namespace QI

noncomputable section Core

variable {X α β γ Ya Yb : Type*} [Fintype X] [Fintype α] [Fintype β] [Fintype γ]
  [Fintype Ya] [Fintype Yb]

/-- The slice of `f` along the cut `e : X ≃ α × Y` at the value `a`: the vector
`y ↦ f (e.symm (a, y))`. -/

theorem core_bound (eA : X ≃ α × Ya) (eB : X ≃ β × Yb)
    (hA : Ya ≃ β × γ) (hB : Yb ≃ α × γ)
    (compat : ∀ (a : α) (b : β) (c : γ), eA.symm (a, hA.symm (b, c)) = eB.symm (b, hB.symm (a, c)))
    (C : Submodule ℂ (EuclideanSpace ℂ X)) (hC : C ≠ ⊥)
    (hcA : CorrCut eA C) (hcB : CorrCut eB C) :
    finrank ℂ C ≤ Fintype.card γ := by
  have h1 : finrank ℂ C * cutRank eA C ≤ Fintype.card γ * cutRank eB C :=
    key_ineq eA eB hA hB compat C hcA
  have h2 : finrank ℂ C * cutRank eB C ≤ Fintype.card γ * cutRank eA C :=
    key_ineq eB eA hB hA (fun b a c => (compat a b c).symm) C hcB
  have hxa : 0 < cutRank eA C := cutRank_pos eA C hC
  have hxb : 0 < cutRank eB C := cutRank_pos eB C hC
  set K := finrank ℂ C
  set g := Fintype.card γ
  set x := cutRank eA C
  set y := cutRank eB C
  have hmul : (K * x) * (K * y) ≤ (g * y) * (g * x) := Nat.mul_le_mul h1 h2
  have hmul' : (K * K) * (x * y) ≤ (g * g) * (x * y) := by
    calc (K * K) * (x * y) = (K * x) * (K * y) := by ring
    _ ≤ (g * y) * (g * x) := hmul
    _ = (g * g) * (x * y) := by ring
  have hpos : 0 < x * y := Nat.mul_pos hxa hxb
  have hKg : K * K ≤ g * g := Nat.le_of_mul_le_mul_right hmul' hpos
  by_contra hcon
  push_neg at hcon
  exact absurd hKg (not_le.mpr (Nat.mul_lt_mul_of_lt_of_le hcon (le_of_lt hcon)
    (lt_of_le_of_lt (Nat.zero_le _) hcon)))

end Core

noncomputable section Concrete

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Merge a configuration on `A` with a configuration on the complement of `A`. -/
