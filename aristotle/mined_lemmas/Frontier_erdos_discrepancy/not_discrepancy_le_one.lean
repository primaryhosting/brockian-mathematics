/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports): a Lean module docstring
must be the first command in a file, so the required header above forces the
file to contain no `import` lines.  Everything below therefore uses only the
Lean 4 core library.  The file `RequestProject/Main.lean` re-states the results
in Mathlib terms (`∑ i ∈ Finset.Icc 1 n, f (i * d)` and `|·|`) and proves that
the two formulations agree.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression with
common difference `d`, over its first `n` terms:  `f d + f (2d) + ⋯ + f (n d)`. -/

theorem not_discrepancy_le_one {f : Nat → Int} (hf : IsPlusMinusOne f)
    (h : ∀ n d : Nat, 1 ≤ n → 1 ≤ d → n * d ≤ 12 → (hapSum f n d).natAbs ≤ 1) :
    False := by
  -- doubling relations: `f (2d) = - f d`, coming from the two-term progressions
  have e2 : f 2 = -f 1 := by
    have h2 := h 2 1 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 1) (hf 2) (by simpa using h2)
  have e4 : f 4 = -f 2 := by
    have h2 := h 2 2 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 2) (hf 4) (by simpa using h2)
  have e6 : f 6 = -f 3 := by
    have h2 := h 2 3 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 3) (hf 6) (by simpa using h2)
  have e8 : f 8 = -f 4 := by
    have h2 := h 2 4 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 4) (hf 8) (by simpa using h2)
  have e10 : f 10 = -f 5 := by
    have h2 := h 2 5 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 5) (hf 10) (by simpa using h2)
  have e12 : f 12 = -f 6 := by
    have h2 := h 2 6 (by omega) (by omega) (by omega)
    rw [hapSum_two] at h2
    exact pm_eq_neg_of_natAbs_add_le_one (hf 6) (hf 12) (by simpa using h2)
  -- the partial sums along `d = 1` and along `d = 3`
  have c4 := h 4 1 (by omega) (by omega) (by omega)
  have c6 := h 6 1 (by omega) (by omega) (by omega)
  have c8 := h 8 1 (by omega) (by omega) (by omega)
  have c10 := h 10 1 (by omega) (by omega) (by omega)
  have c34 := h 4 3 (by omega) (by omega) (by omega)
  rw [hapSum_four_one] at c4
  rw [hapSum_six_one] at c6
  rw [hapSum_eight_one] at c8
  rw [hapSum_ten_one] at c10
  rw [hapSum_four_three] at c34
  have h1 := hf 1
  have h3 := hf 3
  have h5 := hf 5
  have h7 := hf 7
  have h9 := hf 9
  omega

/-- **Base case of the Erdős discrepancy problem (discrepancy `> 1`).**

For every `±1` sequence `f` there are `n, d ≥ 1` with `n * d ≤ 12` such that the
partial sum of `f` along the homogeneous arithmetic progression `d, 2d, …, n d`
has absolute value at least `2`.  Equivalently, no `±1` sequence has discrepancy
at most `1` on homogeneous arithmetic progressions.

This is the `C = 1` case of `Frontier.ErdosDiscrepancyStatement`, the Erdős
discrepancy problem, whose general form is a theorem of Tao.  The bound `12` is
optimal: `Frontier.edsWitness_discrepancy_le_one` (in `RequestProject/Main.lean`)
exhibits a `±1` sequence whose homogeneous-AP partial sums using only indices
`≤ 11` all have absolute value at most `1`. -/
