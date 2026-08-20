import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma finrank_suppSpace {n : ℕ} (H : Finset (Q n)) :
    H.card ≤ Module.finrank ℝ (suppSpace H) := by
  set L := LinearMap.funLeft ℝ ℝ (fun v : {v : Q n // v ∉ H} => (v : Q n)) with hL
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hle : Module.finrank ℝ (LinearMap.range L)
      ≤ Module.finrank ℝ ({v : Q n // v ∉ H} → ℝ) := Submodule.finrank_le _
  have hcard : Module.finrank ℝ ({v : Q n // v ∉ H} → ℝ) = Hᶜ.card := by
    rw [Module.finrank_pi, Fintype.card_subtype]
    congr 1
    ext x
    simp
  have hcc : Hᶜ.card = 2 ^ n - H.card := by
    rw [Finset.card_compl]; simp
  have hHle : H.card ≤ 2 ^ n := by
    have h := Finset.card_le_univ H; simpa using h
  rw [finrank_pi_cube] at hrk
  show H.card ≤ Module.finrank ℝ (LinearMap.ker L)
  omega

/-- The core estimate: an eigenvector with eigenvalue of absolute value `√n`
supported on `H` forces a vertex of `H` of degree at least `√n`. -/
