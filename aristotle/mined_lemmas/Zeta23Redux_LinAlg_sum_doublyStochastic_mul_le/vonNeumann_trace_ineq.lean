import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/

theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    (hmu : ∃ σ : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ σ)
    (hnu : ∃ τ : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ τ)
    (hmu' : Antitone mu) (hnu' : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨σ, rfl⟩ := hmu
  obtain ⟨τ, rfl⟩ := hnu
  set a := hA.eigenvalues
  set b := hB.eigenvalues
  set W : Matrix (Fin d) (Fin d) ℂ :=
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
      * (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hWu : W ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
    mul_mem (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2
  -- the trace is the real number `∑ i, ∑ j, |W i j|² * (a i * b j)`
  have htrace : (Matrix.trace (A * B)).re
      = ∑ i, ∑ j, Complex.normSq (W i j) * (a i * b j) := by
    rw [trace_mul_eq_trace_diag_conj hA hB, trace_diag_conj W a b, Complex.ofReal_re]
  -- the doubly stochastic matrix obtained from `W`, reindexed by the two sorting permutations
  have hS0 : (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) :=
    normSq_mem_doublyStochastic hWu
  rw [mem_doublyStochastic_iff_sum] at hS0
  obtain ⟨hn, hr, hc⟩ := hS0
  have hS : (Matrix.of fun i j => Complex.normSq (W (σ i) (τ j)))
      ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => hn (σ i) (τ j), fun i => ?_, fun j => ?_⟩
    · simpa using (Equiv.sum_comp τ (fun j => Complex.normSq (W (σ i) j))).trans (hr (σ i))
    · simpa using (Equiv.sum_comp σ (fun i => Complex.normSq (W i (τ j)))).trans (hc (τ j))
  have hreindex : ∑ i, ∑ j, Complex.normSq (W i j) * (a i * b j)
      = ∑ i, ∑ j, Complex.normSq (W (σ i) (τ j)) * ((a ∘ σ) i * (b ∘ τ) j) := by
    rw [← Equiv.sum_comp σ (fun i => ∑ j, Complex.normSq (W i j) * (a i * b j))]
    exact Finset.sum_congr rfl fun i _ =>
      (Equiv.sum_comp τ (fun j => Complex.normSq (W (σ i) j) * (a (σ i) * b j))).symm
  rw [htrace, hreindex]
  exact sum_doublyStochastic_mul_le hS hmu' hnu'

/-- Any finite tuple of reals admits a decreasing rearrangement; in particular the hypotheses of
`vonNeumann_trace_ineq` are satisfiable (applied to the eigenvalue tuples). -/
