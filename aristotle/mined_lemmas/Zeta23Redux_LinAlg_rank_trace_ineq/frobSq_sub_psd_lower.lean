/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux
namespace LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a complex matrix. -/

lemma frobSq_sub_psd_lower {P R : Matrix n n ℂ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c * rtrace R - (c ^ 2 / 4) * (P.rank : ℝ) ≤ frobSq (P - R) := by
  set hPh := hP.isHermitian with hPh_def
  set U := hPh.eigenvectorUnitary with hU
  set lam := hPh.eigenvalues with hlam
  set ind : n → ℝ := fun i => if lam i = 0 then 0 else c / 2 with hind
  set comp : n → ℝ := fun i => if lam i = 0 then c / 2 else 0 with hcomp
  have hPsp : P = conjD U lam := spectral_conjD hPh
  set T := conjD U ind with hT
  have hfrobT : frobSq T = (c ^ 2 / 4) * (P.rank : ℝ) := by
    rw [hT, frobSq_conjD, hPh.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rw [show (fun i => (ind i) ^ 2) = (fun i => if lam i ≠ 0 then (c / 2) ^ 2 else 0) by
      funext i; by_cases h : lam i = 0 <;> simp [hind, h]]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero]
    simp only [hlam]
    ring
  have hPT : rtrace (P * T) = (c / 2) * rtrace P := by
    rw [hPsp, hT, conjD_mul, rtrace_conjD, rtrace_conjD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : lam i = 0
    · simp [hind, h]
    · simp only [hind, if_neg h]; ring
  have hRT : rtrace (R * T) ≤ (c / 2) * rtrace R := by
    have hsum : T + conjD U comp = ((c / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
      rw [hT, conjD_add, ← conjD_const U (c / 2)]
      congr 1
      funext i
      by_cases h : lam i = 0 <;> simp [hind, hcomp, h]
    have h1 : rtrace (R * (T + conjD U comp)) = rtrace (R * T) + rtrace (R * conjD U comp) := by
      rw [Matrix.mul_add, rtrace_add]
    rw [hsum, rtrace_smul_one_mul] at h1
    have h2 : 0 ≤ rtrace (R * conjD U comp) := by
      refine rtrace_mul_conjD_nonneg hR U (fun i => ?_)
      by_cases h : lam i = 0
      · simp only [hcomp, if_pos h]; linarith
      · simp [hcomp, h]
    linarith
  have hkey :=
    two_rtrace_sub_frobSq_le (hP.isHermitian.sub hR.isHermitian) (conjD_isHermitian U ind)
  rw [← hT] at hkey
  have hexp : rtrace ((P - R) * T) = rtrace (P * T) - rtrace (R * T) := by
    rw [Matrix.sub_mul, rtrace_sub]
  rw [hexp, hfrobT] at hkey
  linarith

/-- The main inequality. -/
