import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]

theorem weyl_reverse :
    shift d * clock d = Complex.exp (-(2 * Real.pi * Complex.I / d)) • (clock d * shift d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  -- the clock phase advances by one step of `exp (2 π i / d)` under `j ↦ j + 1` in `ZMod d`
  have hstep : ∀ j : ZMod d, Complex.exp (2 * Real.pi * Complex.I * ((j + 1).val : ℂ) / d)
      = Complex.exp (2 * Real.pi * Complex.I / d) *
        Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) := by
    intro j
    rw [← Complex.exp_add]
    have hmod : ((j + 1).val : ℕ) ≡ j.val + 1 [MOD d] :=
      (ZMod.natCast_eq_natCast_iff ((j + 1).val) (j.val + 1) d).mp
        (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ((j.val : ℤ) + 1) - ((j + 1).val : ℤ) = d * k := by
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd (n := d) (a := (j + 1).val) (b := j.val + 1)).mp hmod
      exact ⟨k, by push_cast at hk ⊢; linarith⟩
    have hc : ((j.val : ℂ) + 1) / (d : ℂ) - (((j + 1).val : ℕ) : ℂ) / (d : ℂ) = (k : ℂ) := by
      have h2 : ((j.val : ℂ) + 1) - (((j + 1).val : ℕ) : ℂ) = (d : ℂ) * (k : ℂ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hk
      field_simp
      linear_combination h2
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-k, by push_cast; linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * hc⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp only [shift, clock]
    by_cases h : i = j + 1
    · subst h
      rw [if_pos rfl, hstep j, Complex.exp_neg]
      field_simp
      simp [mul_comm]
    · rw [if_neg h]; ring
  · intro b _ hb; simp [clock, Ne.symm hb]
  · intro h; simp at h
  · intro b _ hb; simp [clock, hb]
  · intro h; simp at h

