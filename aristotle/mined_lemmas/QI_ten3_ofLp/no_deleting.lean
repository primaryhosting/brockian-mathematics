import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Statement: There is no unitary that deletes an unknown quantum state (no-deleting theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- A qubit: the two dimensional complex Hilbert space. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The ancilla register: an `m`-dimensional complex Hilbert space. -/
abbrev Anc (m : ℕ) : Type := EuclideanSpace ℂ (Fin m)

/-- The full register: two qubits together with an `m`-dimensional ancilla,
realized concretely as the Hilbert space with index set `Fin 2 × Fin 2 × Fin m`. -/
abbrev Reg (m : ℕ) : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin m)

/-- The (unnormalized) product state `a ⊗ b ⊗ c` inside `Reg m`. -/

theorem no_deleting {m : ℕ} (blank : Qubit) (anc ancOut : Anc m)
    (hblank : ‖blank‖ = 1) (hanc : ‖anc‖ = 1) (hancOut : ‖ancOut‖ = 1) :
    ¬ ∃ U : Reg m ≃ₗᵢ[ℂ] Reg m,
      ∀ ψ : Qubit, ‖ψ‖ = 1 → U (ten3 ψ ψ anc) = ten3 ψ blank ancOut := by
  rintro ⟨U, hU⟩
  have key : ⟪ten3 psi0 blank ancOut, ten3 psiPlus blank ancOut⟫_ℂ
      = ⟪ten3 psi0 psi0 anc, ten3 psiPlus psiPlus anc⟫_ℂ := by
    rw [← hU psi0 norm_psi0, ← hU psiPlus norm_psiPlus, U.inner_map_map]
  have hb : ⟪blank, blank⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hblank]; norm_num
  have ha : ⟪anc, anc⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hanc]; norm_num
  have hao : ⟪ancOut, ancOut⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hancOut]; norm_num
  rw [inner_ten3, inner_ten3] at key
  simp only [hb, ha, hao, mul_one, inner_psi0_psiPlus] at key
  -- `key` now reads `invSqrtTwo = invSqrtTwo * invSqrtTwo`
  rw [invSqrtTwo_sq] at key
  have hsq := invSqrtTwo_sq
  rw [key] at hsq
  norm_num at hsq

end QI

