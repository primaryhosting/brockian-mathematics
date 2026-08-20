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

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well
of width `L`: `E n = n² π² ℏ² / (2 m L²)`. -/

theorem isBoxEigenstate_boxState (m hbar L : ℝ) (hm : 0 < m) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    IsBoxEigenstate m hbar L (boxEnergy m hbar L n) (boxState L n) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (n : ℝ) * Real.pi / L := ⟨_, rfl⟩
  have hLne : L ≠ 0 := ne_of_gt hL
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hpsi : boxState L n = fun x : ℝ => Real.sin (u * x) := by
    funext x
    simp only [boxState, hu]
    ring_nf
  have h1 : ∀ x : ℝ, HasDerivAt (boxState L n) (u * Real.cos (u * x)) x := by
    intro x
    rw [hpsi]
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul u).sin
  have hd1 : deriv (boxState L n) = fun x : ℝ => u * Real.cos (u * x) :=
    funext fun x => (h1 x).deriv
  have h2 : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => u * Real.cos (u * x)) (-(u ^ 2) * Real.sin (u * x)) x := by
    intro x
    have hcs := (((hasDerivAt_id x).const_mul u).cos).const_mul u
    convert hcs using 1
    simp; ring
  have hd2 : ∀ x : ℝ, deriv (deriv (boxState L n)) x = -(u ^ 2) * Real.sin (u * x) := by
    intro x; rw [hd1]; exact (h2 x).deriv
  have huL : u * L = (n : ℝ) * Real.pi := by rw [hu]; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpsi]
    exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  · intro x
    rw [hd2 x]
    simp only [hpsi, boxEnergy, hu]
    field_simp
  · simp [hpsi]
  · simp only [hpsi, huL]
    exact Real.sin_nat_mul_pi n
  · refine ⟨L / (2 * n), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · have hval : u * (L / (2 * n)) = Real.pi / 2 := by rw [hu]; field_simp
      simp only [hpsi, hval, Real.sin_pi_div_two]
      norm_num

/-- **Particle in a box.** For a particle of mass `m > 0` in an infinite square well of
width `L > 0`, a real number `E` is an energy eigenvalue (i.e. admits a nontrivial
stationary state vanishing at the walls) if and only if
`E = n² π² ℏ² / (2 m L²)` for some integer `n ≥ 1`. -/
