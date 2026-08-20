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

theorem no_nonpositive_eigenvalue (c L : ℝ) (hL : 0 < L) (hc : c ≤ 0) (f f' : ℝ → ℝ)
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf' : ∀ x : ℝ, HasDerivAt f' (-c * f x) x)
    (h0 : f 0 = 0) (hL0 : f L = 0) : ∀ x ∈ Set.Ioo (0 : ℝ) L, f x = 0 := by
  set h : ℝ → ℝ := fun t => f t * f' t with hh
  have hhd : ∀ t : ℝ, HasDerivAt h ((f' t) ^ 2 - c * (f t) ^ 2) t := by
    intro t
    have := (hf t).mul (hf' t)
    convert this using 1
    ring
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg (fun t => (hhd t).differentiableAt)
    intro t
    rw [(hhd t).deriv]
    nlinarith [sq_nonneg (f' t), sq_nonneg (f t)]
  have hzero : ∀ x ∈ Set.Icc (0 : ℝ) L, h x = 0 := by
    intro x hx
    have h1 : h 0 ≤ h x := hmono hx.1
    have h2 : h x ≤ h L := hmono hx.2
    simp only [hh, h0, hL0, zero_mul] at h1 h2
    linarith
  have key : ∀ x ∈ Set.Ioo (0 : ℝ) L, (f' x) ^ 2 - c * (f x) ^ 2 = 0 := by
    intro x hx
    have hev : h =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hzero y (Set.Ioo_subset_Icc_self hy)
    exact (hhd x).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev)
  rcases lt_or_eq_of_le hc with hcneg | hc0
  · intro x hx
    have hkey := key x hx
    have hb : (f x) ^ 2 = 0 := by nlinarith [sq_nonneg (f' x), sq_nonneg (f x)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb
  · subst hc0
    have hx0 : (L / 2) ∈ Set.Ioo (0 : ℝ) L := by constructor <;> linarith
    have hk := key _ hx0
    simp only [zero_mul, sub_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true] at hk
    have hall : ∀ y : ℝ, f' y = 0 := by
      intro y
      have hy := harmonic_invariant 0 f f' hf hf' y (L / 2)
      simp only [zero_mul, add_zero, hk] at hy
      simpa using hy
    have hconst : ∀ y : ℝ, f y = f 0 := fun y =>
      is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
        (fun t => by rw [(hf t).deriv]; exact hall t) y 0
    intro x _
    rw [hconst x, h0]

/-- Quantisation: any nontrivial solution of `f'' = -c f` on `[0, L]` vanishing at the
endpoints forces `c = n²π²/L²` for some `n ≥ 1`. -/
