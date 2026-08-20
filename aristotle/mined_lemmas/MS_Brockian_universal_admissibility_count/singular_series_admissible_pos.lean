import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

theorem singular_series_admissible_pos (G : Finset ℕ)
    (hadm : ∀ p, p.Prime → nu G p < p) (p : ℕ) : 0 < localFactor G p := by
  rw [localFactor]
  split_ifs with hp
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hnum : 0 < 1 - (nu G p : ℝ) / p := by
      have : (nu G p : ℝ) < p := by exact_mod_cast hadm p hp
      rw [sub_pos, div_lt_one hp0]
      exact this
    have hden : 0 < (1 - 1 / (p : ℝ)) ^ G.card := by
      apply pow_pos
      rw [sub_pos, div_lt_one hp0]
      linarith
    exact div_pos hnum hden
  · norm_num
open scoped Classical in
/-- The +3 flow graph on ℤ/n with twin-admissible residues is acyclic (Brockian).
Note: the hypothesis `0 < n` is recorded via the `NeZero n` instance (needed already for the
statement to elaborate, since `ZMod n` is finite only then); `hn` is therefore not used in the
proof, but is kept as given. -/
