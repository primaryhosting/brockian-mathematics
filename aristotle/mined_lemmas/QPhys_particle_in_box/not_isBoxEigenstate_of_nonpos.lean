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

lemma not_isBoxEigenstate_of_nonpos {hbar m L E : ℝ} {psi psi' psi'' : ℝ → ℝ}
    (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (hE : E ≤ 0)
    (h : IsBoxEigenstate hbar m L E psi psi' psi'') : False := by
  obtain ⟨hd, hd', hs, h0, hLL, hnt⟩ := h
  have hb : (hbar : ℝ) ^ 2 ≠ 0 := by positivity
  have hm' : m ≠ 0 := ne_of_gt hm
  have hdiff : Differentiable ℝ psi := fun x => (hd x).differentiableAt
  have hdiff' : Differentiable ℝ psi' := fun x => (hd' x).differentiableAt
  set c : ℝ := -(2 * m * E / hbar ^ 2) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 2 * m * E / hbar ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    linarith
  have heq : ∀ x : ℝ, psi'' x = c * psi x := by
    intro x
    have h := hs x
    rw [hc]
    field_simp at h ⊢
    linarith
  set g : ℝ → ℝ := fun x => psi x * psi' x with hg
  have hdg : ∀ x : ℝ, HasDerivAt g (psi' x ^ 2 + c * psi x ^ 2) x := by
    intro x
    refine ((hd x).mul (hd' x)).congr_deriv ?_
    rw [heq x]; ring
  have hmono : Monotone g :=
    monotone_of_deriv_nonneg (fun x => (hdg x).differentiableAt)
      (fun x => by rw [(hdg x).deriv]; positivity)
  have hgz : ∀ x ∈ Set.Ioo (0 : ℝ) L, g x = 0 := by
    intro x hx
    have h1 : g 0 ≤ g x := hmono hx.1.le
    have h2 : g x ≤ g L := hmono hx.2.le
    have h3 : g 0 = 0 := by simp [hg, h0]
    have h4 : g L = 0 := by simp [hg, hLL]
    linarith
  have hpsi'z : Set.EqOn psi' 0 (Set.Ioo (0 : ℝ) L) := by
    intro x hx
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] g := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using (hgz y hy).symm
    have hd0 : HasDerivAt g 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev.symm
    have huniq := (hdg x).unique hd0
    have hnn : 0 ≤ c * psi x ^ 2 := by positivity
    have hz : psi' x ^ 2 = 0 := by nlinarith [sq_nonneg (psi' x)]
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  have hIcc : Set.EqOn psi' 0 (Set.Icc (0 : ℝ) L) := by
    have := hpsi'z.closure hdiff'.continuous continuous_const
    rwa [closure_Ioo (ne_of_lt hL)] at this
  have hconstpsi : ∀ x ∈ Set.Icc (0 : ℝ) L, psi x = psi 0 := by
    refine constant_of_has_deriv_right_zero hdiff.continuous.continuousOn ?_
    intro x hx
    have hzz : psi' x = 0 := hIcc (Set.mem_Icc_of_Ico hx)
    have h2 := (hd x).hasDerivWithinAt (s := Set.Ici x)
    rwa [hzz] at h2
  obtain ⟨x, hx, hne⟩ := hnt
  exact hne (by rw [hconstpsi x hx, h0])

/-- **Quantization.** Every bound state energy of the infinite square well is one of the
`E_n = n²π²ℏ²/(2mL²)` with `n ≥ 1`. -/
