import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/

theorem exists_eq_boxEnergy {hbar m L E : ℝ} {psi psi' psi'' : ℝ → ℝ}
    (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L)
    (h : IsBoxEigenstate hbar m L E psi psi' psi'') :
    ∃ n : ℕ, 1 ≤ n ∧ E = boxEnergy hbar m L n := by
  rcases le_or_gt E 0 with hEle | hEpos
  · exact absurd h (fun h' => not_isBoxEigenstate_of_nonpos hhbar hm hL hEle h')
  obtain ⟨hd, hd', hs, h0, hLL, hnt⟩ := h
  have hb : (hbar : ℝ) ^ 2 ≠ 0 := by positivity
  have hm' : m ≠ 0 := ne_of_gt hm
  set k : ℝ := Real.sqrt (2 * m * E) / hbar with hkdef
  have hk : 0 < k := by
    rw [hkdef]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) hhbar
  have hk2 : k ^ 2 = 2 * m * E / hbar ^ 2 := by
    rw [hkdef, div_pow, Real.sq_sqrt (by positivity)]
  have heq : ∀ x : ℝ, psi'' x = -(k ^ 2) * psi x := by
    intro x
    have h := hs x
    rw [hk2]
    field_simp at h ⊢
    linarith
  have hsol := eq_sin_of_hasDerivAt hk hd hd' heq h0
  set A : ℝ := psi' 0 / k with hA
  have hA0 : A ≠ 0 := by
    intro hA0
    obtain ⟨x, hx, hne⟩ := hnt
    exact hne (by rw [hsol x, hA0, zero_mul])
  have hsinL : Real.sin (k * L) = 0 := by
    have hL0 := hsol L
    rw [hLL] at hL0
    exact (mul_eq_zero.mp hL0.symm).resolve_left hA0
  obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hsinL
  have hjpos : 0 < j := by
    have hkl : 0 < k * L := mul_pos hk hL
    have h1 : 0 < (j : ℝ) * Real.pi := by rw [hj]; exact hkl
    have h2 : 0 < (j : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast h2
  refine ⟨j.toNat, by omega, ?_⟩
  have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
    have h := Int.toNat_of_nonneg hjpos.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  rw [boxEnergy, hcast]
  have hkL : k = (j : ℝ) * Real.pi / L := by
    field_simp
    linarith [hj]
  have hEk : E = hbar ^ 2 * k ^ 2 / (2 * m) := by
    rw [hk2]; field_simp
  rw [hEk, hkL]
  field_simp

/-- **Particle in a box.** The set of bound-state energies of a particle of mass `m` in an
infinite square well of width `L` is exactly `{ n²π²ℏ²/(2mL²) | n ≥ 1 }`. -/
