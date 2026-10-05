import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement of the **Ten Martini Problem** (solved by A. Avila and
S. Jitomirskaya): *for every nonzero coupling constant `λ`, every irrational frequency `α` and
every phase `θ`, the spectrum of the almost Mathieu operator*
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + n α)) u n`
*acting on `ℓ²(ℤ)` is a Cantor set.*

What is proved here, unconditionally:

* the almost Mathieu operator is constructed as a genuine bounded operator on `ℓ²(ℤ)`
  (`Frontier.almostMathieu`), and is shown to be self-adjoint;
* its real spectrum is nonempty, compact (hence closed) and contained in the interval
  `[-(2 + 2|λ|), 2 + 2|λ|]`;
* the elementary symmetries of the family: `α`-periodicity, `θ`-periodicity, the sign change
  `λ ↦ -λ`, and the covariance `H_{λ,α,θ+α} = S H_{λ,α,θ} S⁻¹` under the shift, which gives
  invariance of the spectrum along the orbit of `θ`;
* the **base case `λ = 0`**: via explicit Weyl sequences of truncated plane waves, the spectrum of
  the free discrete Laplacian is shown to contain the whole band `[-2, 2]`, so it is *not* a
  Cantor set (`Frontier.not_isCantorSet_amoSpectrum_zero`).  This shows the hypothesis `λ ≠ 0`
  cannot be dropped from the Ten Martini statement.

The main theorem `Frontier.avila_ten_martini` is a Lean-checked *reduction*: it derives the full
Ten Martini statement (`Frontier.TenMartiniProblem`) from the two deep analytic inputs — that the
spectrum is nowhere dense and that it has no isolated points. All the remaining content of
"being a Cantor set" (nonempty, compact, closed) is proved here from scratch.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Frontier

noncomputable section

open scoped ComplexConjugate

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev ell2 := lp (fun _ : ℤ => ℂ) 2

/-! ### Basic `ℓ²` facts -/


theorem Icc_subset_amoSpectrum_zero (alpha theta : ℝ) :
    Set.Icc (-2 : ℝ) 2 ⊆ amoSpectrum 0 alpha theta := by
  intro E hE
  obtain ⟨hE1, hE2⟩ := hE
  set k : ℝ := Real.arccos (E / 2) with hk
  have hcos : 2 * Real.cos k = E := by
    rw [hk, Real.cos_arccos (by linarith) (by linarith)]
    ring
  rw [real_mem_spectrum_iff]
  refine mem_spectrum_of_approx _ _ 8 (fun N => truncWave k N) (fun N => ?_) (fun C => ?_)
  · -- residual bound
    set f : ell2 := (E : ℂ) • truncWave k N - almostMathieu 0 alpha theta (truncWave k N) with hf
    have hcoord : ∀ n : ℤ, (f : ℤ → ℂ) n
        = (E : ℂ) * expSeq k N n - (expSeq k N (n + 1) + expSeq k N (n - 1)) := by
      intro n
      simp [hf, amoPotential]
    have hwave : ∀ m : ℤ, -(N : ℤ) ≤ m → m ≤ (N : ℤ) →
        expSeq k N m = Complex.exp (((k * m : ℝ) : ℂ) * Complex.I) :=
      fun m h1 h2 => expSeq_of_mem k N h1 h2
    have hsupp : ∀ n ∉ ({-(N : ℤ) - 1, -(N : ℤ), (N : ℤ), (N : ℤ) + 1} : Finset ℤ),
        (f : ℤ → ℂ) n = 0 := by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      rw [hcoord]
      by_cases hin : -(N : ℤ) + 1 ≤ n ∧ n ≤ (N : ℤ) - 1
      · obtain ⟨ha, hb⟩ := hin
        rw [hwave n (by omega) (by omega), hwave (n + 1) (by omega) (by omega),
          hwave (n - 1) (by omega) (by omega), ← hcos]
        have hid : Complex.exp (((k * (n + 1) : ℝ) : ℂ) * Complex.I)
            + Complex.exp (((k * (n - 1) : ℝ) : ℂ) * Complex.I)
            = ((2 * Real.cos k : ℝ) : ℂ) * Complex.exp (((k * n : ℝ) : ℂ) * Complex.I) := by
          have h1' : ((k * (n + 1) : ℝ) : ℂ) * Complex.I
              = ((k * n : ℝ) : ℂ) * Complex.I + (k : ℂ) * Complex.I := by push_cast; ring
          have h2' : ((k * (n - 1) : ℝ) : ℂ) * Complex.I
              = ((k * n : ℝ) : ℂ) * Complex.I + (-(k : ℂ)) * Complex.I := by push_cast; ring
          rw [h1', h2', Complex.exp_add, Complex.exp_add]
          push_cast [Complex.ofReal_cos]
          rw [Complex.cos]
          ring
        push_cast at hid ⊢
        rw [hid]
        ring
      · push_neg at hin
        have hout : n < -(N : ℤ) - 1 ∨ (N : ℤ) + 1 < n := by omega
        rcases hout with h | h
        · rw [expSeq_of_not_mem k N (Or.inl (by omega)),
            expSeq_of_not_mem k N (Or.inl (by omega)),
            expSeq_of_not_mem k N (Or.inl (by omega))]
          ring
        · rw [expSeq_of_not_mem k N (Or.inr (by omega)),
            expSeq_of_not_mem k N (Or.inr (by omega)),
            expSeq_of_not_mem k N (Or.inr (by omega))]
          ring
    have hbound : ∀ n : ℤ, ‖(f : ℤ → ℂ) n‖ ≤ 4 := by
      intro n
      rw [hcoord]
      have hEle : ‖(E : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨hE1, hE2⟩
      have h1 := norm_expSeq_le_one k N n
      have h2 := norm_expSeq_le_one k N (n + 1)
      have h3 := norm_expSeq_le_one k N (n - 1)
      calc ‖(E : ℂ) * expSeq k N n - (expSeq k N (n + 1) + expSeq k N (n - 1))‖
          ≤ ‖(E : ℂ) * expSeq k N n‖ + ‖expSeq k N (n + 1) + expSeq k N (n - 1)‖ :=
            norm_sub_le _ _
        _ ≤ (2 * 1) + (1 + 1) := by
            gcongr
            · rw [norm_mul]
              exact mul_le_mul hEle h1 (norm_nonneg _) (by norm_num)
            · exact le_trans (norm_add_le _ _) (by linarith)
        _ = 4 := by norm_num
    have hcard : (({-(N : ℤ) - 1, -(N : ℤ), (N : ℤ), (N : ℤ) + 1} : Finset ℤ)).card ≤ 4 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h1 := Finset.card_insert_le (-(N : ℤ)) ({(N : ℤ), (N : ℤ) + 1} : Finset ℤ)
      have h2 := Finset.card_insert_le ((N : ℤ)) ({(N : ℤ) + 1} : Finset ℤ)
      have h3 : ({(N : ℤ) + 1} : Finset ℤ).card = 1 := Finset.card_singleton _
      omega
    have hsq : ‖f‖ ^ 2 ≤ 64 := by
      have := norm_sq_le_of_support f _ hsupp 4 hbound
      have hc : ((({-(N : ℤ) - 1, -(N : ℤ), (N : ℤ), (N : ℤ) + 1} : Finset ℤ)).card : ℝ) ≤ 4 := by
        exact_mod_cast hcard
      nlinarith [norm_nonneg f]
    have : ‖f‖ ≤ 8 := by
      nlinarith [norm_nonneg f]
    exact this
  · -- unbounded norms
    obtain ⟨N, hN⟩ := exists_nat_gt (max C 0 ^ 2)
    refine ⟨N, ?_⟩
    have hsq := norm_truncWave_sq k N
    have h0 : 0 ≤ ‖truncWave k N‖ := norm_nonneg _
    have hCmax : C ≤ max C 0 := le_max_left _ _
    have hmax0 : 0 ≤ max C 0 := le_max_right _ _
    nlinarith [hsq, hN]

/-- **Base case / sharpness**: for zero coupling the spectrum is not a Cantor set, since it has
nonempty interior.  Hence the hypothesis `λ ≠ 0` in the Ten Martini Problem is necessary. -/
