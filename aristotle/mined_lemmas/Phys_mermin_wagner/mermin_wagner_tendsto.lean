/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

theorem mermin_wagner_tendsto (d : ℕ) (hd : d ≤ 2) (β J : ℝ) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (hs : ℕ → ℝ) (Ls : ℕ → ℕ) (hpos : ∀ n, 0 ≤ hs n) (hh : Tendsto hs atTop (nhds 0)) :
    Tendsto (fun n => latticeMag d (Ls n) β J (hs n)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := mermin_wagner d hd β J hβ hJ (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hh δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hlt : hs n < δ := by
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero] at hdist
    exact lt_of_le_of_lt (le_abs_self _) hdist
  have hbound := hmain (hs n) (hpos n) hlt (Ls n)
  rw [Real.dist_eq, sub_zero]
  have : |latticeMag d (Ls n) β J (hs n)| ≤ ε / 2 := hbound
  linarith

end

end Phys

/-
The square lattice box in dimension `d`, its `ℓ^∞` shells, and the harmonic
spin-wave profile with small Dirichlet energy when `d ≤ 2`.
-/
import RequestProject.XY

open MeasureTheory Real

namespace Phys

noncomputable section

/-- The sites of the box `{0,…,2L}^d` in `ℤ^d`. -/
abbrev Site (d L : ℕ) := Fin d → Fin (2 * L + 1)

/-- Distance of a coordinate to the centre `L` of the box. -/
