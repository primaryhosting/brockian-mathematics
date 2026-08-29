import Mathlib
/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/

theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu)
    (pa pb : Equiv.Perm (Fin d))
    (hmuA : mu = hA.eigenvalues ∘ pa) (hnuB : nu = hB.eigenvalues ∘ pb) :
    (A * B).trace.re ≤ ∑ i, mu i * nu i := by
  set a := hA.eigenvalues with ha
  set b := hB.eigenvalues with hb
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set Da : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) with hDa
  set Db : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => ((b i : ℝ) : ℂ)) with hDb
  have hAeq : A = U * Da * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [hU, hDa, ha, Function.comp_def]
  have hBeq : B = V * Db * star V := by
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [hV, hDb, hb, Function.comp_def]
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hW
  have hWu : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    have hUu : U ∈ Matrix.unitaryGroup (Fin d) ℂ := hA.eigenvectorUnitary.2
    have hVu : V ∈ Matrix.unitaryGroup (Fin d) ℂ := hB.eigenvectorUnitary.2
    exact mul_mem (Unitary.star_mem hUu) hVu
  have hstarW : star W = star V * U := by
    rw [hW, Matrix.star_mul, star_star]
  have htr : (A * B).trace = (Da * W * Db * star W).trace := by
    rw [hAeq, hBeq]
    rw [show U * Da * star U * (V * Db * star V) = U * (Da * star U * V * Db * star V) by
      noncomm_ring]
    rw [Matrix.trace_mul_comm]
    congr 1
    rw [hstarW, hW]
    noncomm_ring
  rw [htr, trace_diag_conj a b W, Complex.ofReal_re]
  exact sum_doublyStochastic_le hmu hnu pa pb hmuA hnuB (normSq_mem_doublyStochastic hWu)

/-- Any finite family of reals can be listed in decreasing order, so the hypotheses of
`vonNeumann_trace_ineq` are always satisfiable. -/
