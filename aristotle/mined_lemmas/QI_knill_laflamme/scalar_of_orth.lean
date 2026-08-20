/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : ℕ}

/-! ## Definitions -/

/-- `P` is (the matrix of) an orthogonal projection onto a nonzero code subspace. -/
structure IsCode (P : Matrix (Fin n) (Fin n) ℂ) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  ne_zero : P ≠ 0

/-- The Knill–Laflamme conditions for a code with projection `P` and error operators `E`:
there is a matrix of scalars `c` with `P Eₐ† E_b P = c a b • P`. -/

theorem scalar_of_orth (v ψ : Fin n → ℂ) (hψ : ψ ≠ 0)
    (key : ∀ phi : Fin n → ℂ, star phi ⬝ᵥ ψ = 0 → star phi ⬝ᵥ v = 0) :
    ∃ t : ℂ, v = t • ψ := by
  set nrm : ℂ := star ψ ⬝ᵥ ψ with hnrm
  have hnrm0 : nrm ≠ 0 := fun h => hψ (dotProduct_star_self_eq_zero.1 h)
  have hnrmconj : (starRingEnd ℂ) nrm = nrm := by rw [hnrm, ← star_dotProduct_comm ψ ψ]
  refine ⟨(star ψ ⬝ᵥ v) / nrm, ?_⟩
  set c : ℂ := (star ψ ⬝ᵥ v) / nrm with hc
  set phi : Fin n → ℂ := v - c • ψ with hphi
  have hcconj : (starRingEnd ℂ) c = (star v ⬝ᵥ ψ) / nrm := by
    rw [hc, map_div₀, hnrmconj, ← star_dotProduct_comm ψ v]
  have hphiψ : star phi ⬝ᵥ ψ = 0 := by
    rw [hphi]
    simp only [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [RCLike.star_def, hcconj, ← hnrm]
    field_simp
    ring
  have h1 : star phi ⬝ᵥ v = 0 := key phi hphiψ
  have h2 : star phi ⬝ᵥ phi = 0 := by
    rw [hphi, dotProduct_sub, ← hphi, h1, dotProduct_smul, smul_eq_mul, hphiψ]; ring
  have h3 : phi = 0 := dotProduct_star_self_eq_zero.1 h2
  rw [hphi] at h3
  exact sub_eq_zero.1 h3

/-- If a family of Kraus operators maps the rank-one operator `ψψ†` to itself, then each
operator acts on `ψ` as a scalar. -/
