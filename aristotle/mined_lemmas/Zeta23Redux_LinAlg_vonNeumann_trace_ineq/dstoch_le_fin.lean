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

lemma dstoch_le_fin {d : ℕ} (mu nu : Fin d → ℝ) (T : Fin d → Fin d → ℝ)
    (hT0 : ∀ i j, 0 ≤ T i j)
    (hTrow : ∀ i, ∑ j, T i j = 1) (hTcol : ∀ j, ∑ i, T i j = 1)
    (hmuAnti : Antitone mu) (hnuAnti : Antitone nu) :
    ∑ i, ∑ j, mu i * nu j * T i j ≤ ∑ i, mu i * nu i := by
  set m : ℕ → ℝ := fun i => if h : i < d then mu ⟨i, h⟩ else 0 with hm'
  set n : ℕ → ℝ := fun j => if h : j < d then nu ⟨j, h⟩ else 0 with hn'
  set S : ℕ → ℕ → ℝ := fun i j =>
    if hi : i < d then (if hj : j < d then T ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0 with hS'
  have key := dstoch_le d S m n ?_ ?_ ?_ ?_ ?_
  · have hR : ∑ i ∈ range d, m i * n i = ∑ i, mu i * nu i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => m i * n i) d]
      exact Finset.sum_congr rfl fun i _ => by simp [hm', hn']
    have hL : ∑ i ∈ range d, ∑ j ∈ range d, m i * n j * S i j
        = ∑ i, ∑ j, mu i * nu j * T i j := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range d, m i * n j * S i j) d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun j => m i * n j * S i j) d]
      exact Finset.sum_congr rfl fun j _ => by simp [hm', hn', hS']
    rw [hL, hR] at key
    exact key
  · intro i j hi hj; simp [hS', hi, hj, hT0]
  · intro i hi
    rw [← Fin.sum_univ_eq_sum_range (fun j => S i j) d]
    rw [show (∑ j : Fin d, S i j) = ∑ j : Fin d, T ⟨i, hi⟩ j from
      Finset.sum_congr rfl fun j _ => by simp [hS', hi]]
    exact hTrow ⟨i, hi⟩
  · intro j hj
    rw [← Fin.sum_univ_eq_sum_range (fun i => S i j) d]
    rw [show (∑ i : Fin d, S i j) = ∑ i : Fin d, T i ⟨j, hj⟩ from
      Finset.sum_congr rfl fun i _ => by simp [hS', hj]]
    exact hTcol ⟨j, hj⟩
  · intro i j hij hjd
    have hid : i < d := by omega
    simp only [hm', dif_pos hid, dif_pos hjd]
    exact hmuAnti hij
  · intro i j hij hjd
    have hid : i < d := by omega
    simp only [hn', dif_pos hid, dif_pos hjd]
    exact hnuAnti hij

/-- The trace of `diag x * W * diag y * Wᴴ` in terms of the entrywise squared moduli of `W`. -/
