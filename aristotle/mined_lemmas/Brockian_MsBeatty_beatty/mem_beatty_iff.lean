import Mathlib
namespace Brockian.MsBeatty

/-- Hölder conjugacy from the hypotheses `1 < r` and `1/r + 1/s = 1`. -/

private lemma mem_beatty_iff (t : ℝ) (n : ℤ) :
    n ∈ {beattySeq t k | k > 0} ↔ ∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * t⌋ = n := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.toNat, by omega, ?_⟩
    have h : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
    rw [h]; rfl
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(m : ℤ), by exact_mod_cast hm, by simp [beattySeq]⟩

/-- Rayleigh–Beatty theorem: if 1/r + 1/s = 1 with r > 1 irrational, the Beatty sequences ⌊n·r⌋
    and ⌊n·s⌋ partition the positive integers — each n > 0 is hit by exactly one. -/
