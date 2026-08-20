/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix
open scoped Kronecker MatrixOrder

variable {n m : ℕ}

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C = ∑ i j, E i j ⊗ Φ (E i j)`, i.e. `C (i, a) (j, b) = Φ (E i j) a b`. -/

lemma hasKraus_of_choiMatrix_posSemidef (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun r => Matrix.of fun a i => star (B r (i, a)), ?_⟩
  intro X
  ext a b
  have hC : ∀ i j, (Φ (Matrix.single i j 1)) a b
      = ∑ r, star (B r (i, a)) * B r (j, b) := by
    intro i j
    have := congrArg (fun M => M (i, a) (j, b)) hB
    simp [choiMatrix, Matrix.mul_apply] at this ⊢
    rw [this]
  have key : ∀ f : Fin n → Fin n → (Fin n × Fin m) → ℂ,
      ∑ i, ∑ j, ∑ r, f i j r = ∑ r, ∑ j, ∑ i, f i j r := fun f =>
    calc ∑ i, ∑ j, ∑ r, f i j r = ∑ i, ∑ r, ∑ j, f i j r :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r, ∑ i, ∑ j, f i j r := Finset.sum_comm
      _ = ∑ r, ∑ j, ∑ i, f i j r := Finset.sum_congr rfl fun r _ => Finset.sum_comm
  rw [apply_eq_sum_single Φ X]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, hC, star_star, Finset.sum_mul, Finset.mul_sum]
  refine Eq.trans (key _) ?_
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

/-- The (unnormalized) maximally entangled state `∑ i j, E i j ⊗ E i j`. -/
