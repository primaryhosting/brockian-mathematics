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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/

lemma key_decomp {U P N : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (m : Fin d → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hP : P = U * Matrix.diagonal (fun i => (m i : ℂ)) * Uᴴ)
    {k : ℕ} (hk : (Finset.univ.filter (fun i => m i ≠ 0)).card ≤ k)
    (hN : N.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    c * rtrace P - (c ^ 2 / 4) * k + 2 * rtrace (P * N)
      ≤ frobSq P + frobSq N + c * rtrace N := by
  have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by simpa using hU'
  set W : Matrix (Fin d) (Fin d) ℂ := Uᴴ * N * U with hWdef
  have hWpsd : W.PosSemidef := by
    have h := hN.mul_mul_conjTranspose_same (Uᴴ)
    rw [hWdef]
    simpa using h
  set w : Fin d → ℝ := fun i => (W i i).re with hwdef
  have hw : ∀ i, 0 ≤ w i := fun i => psd_diag_re_nonneg hWpsd i
  have h1 : rtrace P = ∑ i, m i := by rw [hP, rtrace_conj hU, rtrace_diagonal]
  have h2 : frobSq P = ∑ i, (m i) ^ 2 := by rw [hP, frobSq_conj hU, frobSq_diagonal]
  have h3 : rtrace (P * N) = ∑ i, m i * w i := rtrace_mul_of_decomp hU hU' m hP
  have hWN : Uᴴ * N * (Uᴴ)ᴴ = W := by rw [hWdef]; simp
  have h4 : rtrace N = ∑ i, w i := by
    have h := rtrace_conj (U := Uᴴ) (X := N) hUH
    rw [hWN] at h
    rw [← h, rtrace_eq_sum_diag]
  have h5 : ∑ i, (w i) ^ 2 ≤ frobSq N := by
    have hfrob : frobSq W = frobSq N := by
      have h := frobSq_conj (U := Uᴴ) (X := N) hUH
      rw [hWN] at h
      exact h
    calc ∑ i, (w i) ^ 2 = ∑ i, ‖W i i‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [psd_diag_norm hWpsd i]
      _ ≤ frobSq W := sum_diag_sq_le_frobSq W
      _ = frobSq N := hfrob
  have hs := scalar_key m w hm hw hk hc
  rw [h1, h2, h3, h4]
  linarith

/-- Positive semidefinite matrices have nonnegative trace pairing. -/
