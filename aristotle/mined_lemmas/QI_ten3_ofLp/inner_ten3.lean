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

lemma inner_ten3 {m : ℕ} (a b : Qubit) (c : Anc m) (a' b' : Qubit) (c' : Anc m) :
    ⟪ten3 a b c, ten3 a' b' c'⟫_ℂ = ⟪a, a'⟫_ℂ * ⟪b, b'⟫_ℂ * ⟪c, c'⟫_ℂ := by
  have hprod : ∀ f : Fin 2 → ℂ, ∀ g : Fin 2 → ℂ, ∀ h : Fin m → ℂ,
      ∑ p : Fin 2 × Fin 2 × Fin m, f p.1 * g p.2.1 * h p.2.2
        = (∑ i, f i) * (∑ j, g j) * (∑ k, h k) := by
    intro f g h
    simp_rw [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [PiLp.inner_apply, RCLike.inner_apply, ten3_ofLp, map_mul]
  have := hprod (fun i => a'.ofLp i * (starRingEnd ℂ) (a.ofLp i))
    (fun j => b'.ofLp j * (starRingEnd ℂ) (b.ofLp j))
    (fun k => c'.ofLp k * (starRingEnd ℂ) (c.ofLp k))
  rw [← this]
  exact Finset.sum_congr rfl (fun p _ => by ring)

/-- The scalar `1/√2`, viewed as a complex number. -/
