/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20adj_mulVec_pow {a : ℂ} (ha : a ^ 20 = 1) :
    C20adj *ᵥ (fun i : ZMod 20 => a ^ i.val) = (a + a⁻¹) • (fun i : ZMod 20 => a ^ i.val) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hv1 : (1 : ZMod 20).val = 1 := rfl
  funext i
  rw [C20adj_mulVec]
  have h1 : a ^ (i + 1).val = a ^ i.val * a := by
    rw [pow_val_add ha, hv1, pow_one]
  have h2 : a ^ (i - 1).val * a = a ^ i.val := by
    have h := pow_val_add ha (i - 1) 1
    rw [sub_add_cancel, hv1, pow_one] at h
    rw [h]
  have h2' : a ^ (i - 1).val = a ^ i.val * a⁻¹ := by
    field_simp at h2 ⊢
    linear_combination h2
  simp only [Pi.smul_apply, smul_eq_mul, h1, h2']
  ring

/-- The primitive 20-th root of unity `exp (2πi k / 20)` attached to `k`. -/
