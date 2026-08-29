/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- **Rearrangement against a doubly stochastic matrix.** If `S` is doubly stochastic and
`mu`, `nu` are both antitone, then the bilinear form `∑ i j, mu i * S i j * nu j` is at most
the aligned sum `∑ i, mu i * nu i`.  Proved via Birkhoff's theorem plus the rearrangement
inequality. -/

theorem exists_doublyStochastic_trace_eq {d : ℕ} {A B U V : Matrix (Fin d) (Fin d) ℂ}
    {a b : Fin d → ℝ}
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) (hV : V * Vᴴ = 1) (hV' : Vᴴ * V = 1)
    (hA : A = U * diagonal (fun i => (a i : ℂ)) * Uᴴ)
    (hB : B = V * diagonal (fun i => (b i : ℂ)) * Vᴴ) :
    ∃ S : Matrix (Fin d) (Fin d) ℝ, S ∈ doublyStochastic ℝ (Fin d) ∧
      (Matrix.trace (A * B)).re = ∑ i, ∑ j, a i * S i j * b j := by
  set W : Matrix (Fin d) (Fin d) ℂ := Uᴴ * V with hWdef
  have hWH : Wᴴ = Vᴴ * U := by
    simp [hWdef, Matrix.conjTranspose_mul]
  have hWW : W * Wᴴ = 1 := by
    rw [hWdef, hWH]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hV]; simp [hU']
  have hWW' : Wᴴ * W = 1 := by
    rw [hWdef, hWH]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hU]; simp [hV']
  refine ⟨Matrix.of fun i j => Complex.normSq (W i j),
    normSq_mem_doublyStochastic hWW hWW', ?_⟩
  have htr : Matrix.trace (A * B)
      = ((∑ i, ∑ j, a i * b j * Complex.normSq (W i j) : ℝ) : ℂ) := by
    rw [← trace_diagonal_mul_conjTranspose a b W]
    rw [hA, hB]
    rw [show U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun i => (b i : ℂ)) * Vᴴ)
        = U * (diagonal (fun i => (a i : ℂ)) * Uᴴ * V * diagonal (fun i => (b i : ℂ)) * Vᴴ) by
      simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    congr 1
    rw [hWH, hWdef]
    simp [Matrix.mul_assoc]
  rw [htr, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Matrix.of_apply]; ring

/-- **Von Neumann's trace inequality** for Hermitian complex matrices.
If `A` and `B` are Hermitian `d × d` complex matrices and `mu`, `nu` list the eigenvalues of
`A` and `B` respectively (as rearrangements `sA`, `sB` of `Matrix.IsHermitian.eigenvalues`),
both in decreasing order, then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
