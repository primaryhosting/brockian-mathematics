/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/

theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (mu nu : Fin d → ℝ) (sA sB : Equiv.Perm (Fin d))
    (hmu : ∀ i, mu i = hA.eigenvalues (sA i))
    (hnu : ∀ i, nu i = hB.eigenvalues (sB i))
    (hmuAnti : Antitone mu) (hnuAnti : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  rw [trace_mul_eq_conj_diag hA hB, trace_conj_diag]
  simp only [Complex.re_sum, Complex.ofReal_re]
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hW
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hVV : star V * V = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hVV' : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hB.eigenvectorUnitary.2
  have hWs : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hW1 : W * star W = 1 := by
    rw [hW, hWs]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp [mul_assoc]
      _ = 1 := by rw [hVV', mul_one, hUU]
  have hW2 : star W * W = 1 := by
    rw [hW, hWs]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp [mul_assoc]
      _ = 1 := by rw [hUU', mul_one, hVV]
  have reindex : ∑ k, ∑ l, hA.eigenvalues k * hB.eigenvalues l * Complex.normSq (W k l)
      = ∑ i, ∑ j, mu i * nu j * Complex.normSq (W (sA i) (sB j)) := by
    rw [← Equiv.sum_comp sA
      (fun k => ∑ l, hA.eigenvalues k * hB.eigenvalues l * Complex.normSq (W k l))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp sB
      (fun l => hA.eigenvalues (sA i) * hB.eigenvalues l * Complex.normSq (W (sA i) l))]
    exact Finset.sum_congr rfl fun j _ => by rw [hmu, hnu]
  rw [reindex]
  refine dstoch_le_fin mu nu (fun i j => Complex.normSq (W (sA i) (sB j)))
    (fun i j => Complex.normSq_nonneg _) ?_ ?_ hmuAnti hnuAnti
  · intro i
    rw [Equiv.sum_comp sB (fun l => Complex.normSq (W (sA i) l))]
    exact normSq_row_sum W hW1 _
  · intro j
    rw [Equiv.sum_comp sA (fun k => Complex.normSq (W k (sB j)))]
    exact normSq_col_sum W hW2 _

/-- Every finite tuple of reals can be reindexed by a permutation so as to become decreasing. -/
