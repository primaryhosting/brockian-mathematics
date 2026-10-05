import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

theorem posSemidef_of_frame {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu)
    {rho : Matrix (Fin n) (Fin n) ℂ} (hrho : rho.IsHermitian)
    (hframe : ∀ v : Fin n → ℂ, IsUnitVec v →
      ((mu (rankOneProj v) : ℝ) : ℂ) = (rho * rankOneProj v).trace) :
    rho.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hrho fun x => ?_
  set r : ℝ := ∑ i, Complex.normSq (x i) with hrdef
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hxx : star x ⬝ᵥ x = (r : ℂ) := by
    rw [hrdef, dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by
      simp [Complex.normSq_eq_conj_mul_self]
  by_cases hx : r = 0
  · have hx0 : x = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ Finset.univ) => Complex.normSq_nonneg (x i))).mp (hrdef ▸ hx) i
        (Finset.mem_univ i)
      exact Complex.normSq_eq_zero.mp this
    simp [hx0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hx)
    set t : ℝ := Real.sqrt r with htdef
    have htpos : 0 < t := Real.sqrt_pos.mpr hrpos
    have htt : t * t = r := Real.mul_self_sqrt hr0
    have ht2 : (t : ℂ) * (t : ℂ) = (r : ℂ) := by exact_mod_cast congrArg (fun s : ℝ => (s : ℂ)) htt
    set c : ℂ := ((t : ℂ))⁻¹ with hcdef
    have hcc : star c * c = ((r : ℂ))⁻¹ := by
      rw [hcdef, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ht2]
    set v : Fin n → ℂ := c • x with hvdef
    have hv : IsUnitVec v := by
      rw [IsUnitVec, hvdef, dotProduct_self_smul, hcc, hxx, inv_mul_cancel₀]
      exact_mod_cast hrpos.ne'
    have hkey : star v ⬝ᵥ (rho *ᵥ v) = ((r : ℂ))⁻¹ * (star x ⬝ᵥ (rho *ᵥ x)) := by
      rw [hvdef, dotProduct_mulVec_smul, hcc]
    have hframe' := hframe v hv
    rw [trace_mul_rankOneProj] at hframe'
    have hfinal : star x ⬝ᵥ (rho *ᵥ x) = ((r * mu (rankOneProj v) : ℝ) : ℂ) := by
      have : (r : ℂ) * (star v ⬝ᵥ (rho *ᵥ v)) = star x ⬝ᵥ (rho *ᵥ x) := by
        rw [hkey, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hrpos.ne' : (r : ℂ) ≠ 0),
          one_mul]
      rw [← this, ← hframe']
      push_cast
      ring
    rw [hfinal]
    have : (0 : ℝ) ≤ r * mu (rankOneProj v) :=
      mul_nonneg hr0 (hmu.nonneg _ (isProj_rankOneProj hv))
    exact_mod_cast this

/-- The reduction of Gleason's theorem to its analytic core:  once the quantum measure is
known to be a quadratic form on rank-one projections, it is the trace against a genuine
density operator. -/
