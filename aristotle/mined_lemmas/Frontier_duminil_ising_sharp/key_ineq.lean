/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## Sharpness of the phase transition (Duminil-Copin–Tassion)

The analytic engine behind Duminil-Copin's proof of sharpness of the phase transition for the
Ising model (and Bernoulli percolation) is a differential inequality of the form

  `(f n)' (p) ≥ (n / ∑_{k < n} f k (p)) · f n (p) · (1 - f n (p))`,

where `f n (p)` is a finite-volume order parameter at scale `n` (e.g. the two-point function
`⟨σ₀ σ_{∂Λ_n}⟩_β`, or the probability of a connection to the boundary of the box of size `n`)
at parameter `p` (playing the role of the inverse temperature).

Below we formalise this setting abstractly (`Frontier.IsDCTFamily`), define the critical
parameter as the supremum of the parameters at which the order parameters are summable
(`Frontier.criticalPoint`), and prove the **sharpness dichotomy**: strictly below the critical
parameter the order parameters decay *exponentially* fast, while strictly above it they are not
even summable, so in particular no exponential decay can hold. There is no intermediate regime.
-/

/-- The hypotheses of the Duminil-Copin–Tassion differential inequality.
`f n` is a finite-volume order parameter at scale `n`, taking values in `[0,1]`, nondecreasing
in the parameter `p ∈ [0,1]`, differentiable with derivative `fd n`, and satisfying the
differential inequality `n · f n p · (1 - f n p) ≤ (∑_{k < n} f k p) · (f n)' p`. -/
structure IsDCTFamily (f fd : ℕ → ℝ → ℝ) : Prop where
  /-- The order parameters take values in `[0,1]`. -/
  mem_Icc : ∀ (n : ℕ), ∀ p ∈ Set.Icc (0 : ℝ) 1, f n p ∈ Set.Icc (0 : ℝ) 1
  /-- The order parameters are nondecreasing in the parameter. -/
  mono : ∀ (n : ℕ), MonotoneOn (f n) (Set.Icc (0 : ℝ) 1)
  /-- `fd n` is the derivative of `f n`. -/
  hasDeriv : ∀ (n : ℕ), ∀ p ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt (f n) (fd n p) (Set.Icc (0 : ℝ) 1) p
  /-- The Duminil-Copin–Tassion differential inequality. -/
  ineq : ∀ (n : ℕ), 1 ≤ n → ∀ p ∈ Set.Icc (0 : ℝ) 1,
    (n : ℝ) * f n p * (1 - f n p) ≤ (∑ k ∈ Finset.range n, f k p) * fd n p

/-- The critical parameter of a family of order parameters: the supremum of the set of
parameters in `[0,1]` at which the order parameters are summable. -/

lemma key_ineq (h : IsDCTFamily f fd) {n : ℕ} (hn : 1 ≤ n) {p q S : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) (hS : 0 < S)
    (hSb : ∀ s ∈ Set.Icc p q, (∑ k ∈ Finset.range n, f k s) ≤ S) :
    f n p * (1 - f n q) ≤ f n q * (1 - f n p) * Real.exp (-((n : ℝ) * (q - p) / S)) := by
  have hsub : Set.Icc p q ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨le_trans hp hx.1, le_trans hx.2 hq⟩
  have hpI : p ∈ Set.Icc (0 : ℝ) 1 := hsub ⟨le_refl p, hpq⟩
  have hqI : q ∈ Set.Icc (0 : ℝ) 1 := hsub ⟨hpq, le_refl q⟩
  have hfp := h.mem_Icc n p hpI
  have hfq := h.mem_Icc n q hqI
  have hexp : (0 : ℝ) < Real.exp (-((n : ℝ) * (q - p) / S)) := Real.exp_pos _
  -- degenerate case `f n p = 0`
  rcases eq_or_lt_of_le hfp.1 with hzero | hppos
  · rw [← hzero, zero_mul, sub_zero]
    exact mul_nonneg (mul_nonneg hfq.1 zero_le_one) hexp.le
  -- degenerate case `f n q = 1`
  rcases eq_or_lt_of_le hfq.2 with hone | hqlt
  · rw [hone]
    have h1 : (0 : ℝ) ≤ 1 - f n p := by linarith [hfp.2]
    nlinarith [hexp]
  -- main case : `0 < f n p` and `f n q < 1`
  have hbounds : ∀ x ∈ Set.Icc p q, 0 < f n x ∧ f n x < 1 := by
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := hsub hx
    have h1 : f n p ≤ f n x := h.mono n hpI hxI hx.1
    have h2 : f n x ≤ f n q := h.mono n hxI hqI hx.2
    exact ⟨lt_of_lt_of_le hppos h1, lt_of_le_of_lt h2 hqlt⟩
  set c : ℝ := (n : ℝ) / S with hc
  set ψ : ℝ → ℝ := fun x => Real.log (f n x) - Real.log (1 - f n x) - c * x with hψ
  have hmonoψ : MonotoneOn ψ (Set.Icc p q) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p q)
    · -- continuity
      intro x hx
      have hxI : x ∈ Set.Icc (0 : ℝ) 1 := hsub hx
      have hcont : ContinuousWithinAt (f n) (Set.Icc p q) x :=
        ((h.hasDeriv n x hxI).continuousWithinAt).mono hsub
      have hb := hbounds x hx
      have h1 : ContinuousWithinAt (fun y : ℝ => Real.log (f n y)) (Set.Icc p q) x :=
        hcont.log (ne_of_gt hb.1)
      have hne : (1 : ℝ) - f n x ≠ 0 := by linarith [hb.2]
      have hcont' : ContinuousWithinAt (fun y : ℝ => 1 - f n y) (Set.Icc p q) x :=
        (continuousWithinAt_const (b := (1 : ℝ))).sub hcont
      have h2 : ContinuousWithinAt (fun y : ℝ => Real.log (1 - f n y)) (Set.Icc p q) x :=
        hcont'.log hne
      rw [hψ]
      exact (h1.sub h2).sub (continuousWithinAt_const.mul continuousWithinAt_id)
    · -- differentiability on the interior
      intro x hx
      rw [interior_Icc] at hx
      have hxI : x ∈ Set.Icc (0 : ℝ) 1 := hsub (Set.Ioo_subset_Icc_self hx)
      have hb := hbounds x (Set.Ioo_subset_Icc_self hx)
      have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds x := by
        have hx0 : (0 : ℝ) < x := lt_of_le_of_lt hp hx.1
        have hx1 : x < 1 := lt_of_lt_of_le hx.2 hq
        exact Filter.mem_of_superset (Ioo_mem_nhds hx0 hx1) Set.Ioo_subset_Icc_self
      have hd : HasDerivAt (f n) (fd n x) x := (h.hasDeriv n x hxI).hasDerivAt hnhds
      have h1 : HasDerivAt (fun y : ℝ => Real.log (f n y)) (fd n x / f n x) x :=
        hd.log (ne_of_gt hb.1)
      have hne : (1 : ℝ) - f n x ≠ 0 := by linarith [hb.2]
      have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - f n y)) (-fd n x / (1 - f n x)) x := by
        simpa using ((hd.const_sub (1 : ℝ)).log hne)
      have hlin : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have h3 : HasDerivAt ψ (fd n x / f n x - -fd n x / (1 - f n x) - c) x := by
        rw [hψ]
        exact (h1.sub h2).sub hlin
      exact (h3.differentiableAt).differentiableWithinAt
    · -- the derivative is nonnegative
      intro x hx
      rw [interior_Icc] at hx
      have hxI : x ∈ Set.Icc (0 : ℝ) 1 := hsub (Set.Ioo_subset_Icc_self hx)
      have hb := hbounds x (Set.Ioo_subset_Icc_self hx)
      have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds x := by
        have hx0 : (0 : ℝ) < x := lt_of_le_of_lt hp hx.1
        have hx1 : x < 1 := lt_of_lt_of_le hx.2 hq
        exact Filter.mem_of_superset (Ioo_mem_nhds hx0 hx1) Set.Ioo_subset_Icc_self
      have hd : HasDerivAt (f n) (fd n x) x := (h.hasDeriv n x hxI).hasDerivAt hnhds
      have h1 : HasDerivAt (fun y : ℝ => Real.log (f n y)) (fd n x / f n x) x :=
        hd.log (ne_of_gt hb.1)
      have hne : (1 : ℝ) - f n x ≠ 0 := by linarith [hb.2]
      have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - f n y)) (-fd n x / (1 - f n x)) x := by
        simpa using ((hd.const_sub (1 : ℝ)).log hne)
      have hlin : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have h3 : HasDerivAt ψ (fd n x / f n x - -fd n x / (1 - f n x) - c) x := by
        rw [hψ]
        exact (h1.sub h2).sub hlin
      rw [h3.deriv]
      -- an algebraic computation
      have hsig : (∑ k ∈ Finset.range n, f k x) ≤ S := hSb x (Set.Ioo_subset_Icc_self hx)
      have hsig0 : 0 ≤ ∑ k ∈ Finset.range n, f k x := partialSum_nonneg h n hxI
      have hDCT := h.ineq n hn x hxI
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      have hu : 0 < f n x := hb.1
      have hu1 : 0 < 1 - f n x := by linarith [hb.2]
      have hpos : 0 < (n : ℝ) * f n x * (1 - f n x) := by positivity
      have hsigpos : 0 < ∑ k ∈ Finset.range n, f k x := by
        rcases eq_or_lt_of_le hsig0 with heq | hlt
        · exfalso
          rw [← heq, zero_mul] at hDCT
          linarith
        · exact hlt
      have hfdpos : 0 < fd n x := by
        by_contra hcon
        push_neg at hcon
        nlinarith [mul_nonneg hsigpos.le (neg_nonneg.mpr hcon)]
      have hkey : (n : ℝ) * f n x * (1 - f n x) ≤ S * fd n x := by
        nlinarith [mul_le_mul_of_nonneg_right hsig hfdpos.le]
      have hstep : c ≤ fd n x / (f n x * (1 - f n x)) := by
        rw [hc, div_le_div_iff₀ hS (by positivity)]
        nlinarith
      have hsplit : fd n x / f n x - -fd n x / (1 - f n x)
          = fd n x / (f n x * (1 - f n x)) := by
        field_simp
        ring
      rw [hsplit]
      linarith
  have hle : ψ p ≤ ψ q := hmonoψ ⟨le_refl p, hpq⟩ ⟨hpq, le_refl q⟩ hpq
  -- unwind the logarithms
  have hbp := hbounds p ⟨le_refl p, hpq⟩
  have hbq := hbounds q ⟨hpq, le_refl q⟩
  have ha : 0 < f n p * (1 - f n q) := mul_pos hbp.1 (by linarith [hbq.2])
  have hbb : 0 < f n q * (1 - f n p) := mul_pos hbq.1 (by linarith [hbp.2])
  have hlog : Real.log (f n p * (1 - f n q))
      ≤ Real.log (f n q * (1 - f n p)) + (-((n : ℝ) * (q - p) / S)) := by
    rw [Real.log_mul (ne_of_gt hbp.1) (by linarith [hbq.2] : (1 : ℝ) - f n q ≠ 0),
      Real.log_mul (ne_of_gt hbq.1) (by linarith [hbp.2] : (1 : ℝ) - f n p ≠ 0)]
    have hcq : c * (q - p) = (n : ℝ) * (q - p) / S := by
      rw [hc]; ring
    simp only [hψ] at hle
    linarith [hle, hcq]
  calc f n p * (1 - f n q)
      = Real.exp (Real.log (f n p * (1 - f n q))) := (Real.exp_log ha).symm
    _ ≤ Real.exp (Real.log (f n q * (1 - f n p)) + (-((n : ℝ) * (q - p) / S))) :=
        Real.exp_le_exp.2 hlog
    _ = f n q * (1 - f n p) * Real.exp (-((n : ℝ) * (q - p) / S)) := by
        rw [Real.exp_add, Real.exp_log hbb]

/-- **Exponential decay below a point of summability.**  If the order parameters are summable at
`q` and `0 ≤ p < q ≤ 1`, then they decay exponentially fast at `p`. -/
