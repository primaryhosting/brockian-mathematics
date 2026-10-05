import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- `GoldbachPair n` says that `n` is a sum of two primes. -/
def GoldbachPair (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The finite set of ordered Goldbach representations of `n`: pairs of primes summing to `n`. -/
def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => Nat.Prime p.1 ∧ Nat.Prime p.2 ∧ p.1 + p.2 = n)

/-- The spectral count of `n`: the number of ordered Goldbach representations of `n`,
viewed as a real number.  This is the quantity a "spectral model" is supposed to describe. -/
noncomputable def spectralCount (n : ℕ) : ℝ := ((reps n).card : ℝ)

lemma mem_reps {n p q : ℕ} :
    (p, q) ∈ reps n ↔ Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  constructor
  · intro h
    simp only [reps, Finset.mem_filter] at h
    exact h.2
  · rintro ⟨hp, hq, hpq⟩
    simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, hp, hq, hpq⟩

/-- A positive spectral count at `n` produces an actual Goldbach representation of `n`. -/
lemma goldbachPair_of_spectralCount_pos {n : ℕ} (h : 0 < spectralCount n) :
    GoldbachPair n := by
  have hcard : 0 < (reps n).card := by
    have hne : ((reps n).card : ℝ) ≠ 0 := ne_of_gt h
    exact Nat.pos_of_ne_zero fun hz => hne (by simp [hz])
  obtain ⟨⟨p, q⟩, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨p, q, mem_reps.mp hx⟩

/-- Conversely, a Goldbach representation makes the spectral count positive. -/
lemma spectralCount_pos_of_goldbachPair {n : ℕ} (h : GoldbachPair n) :
    0 < spectralCount n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  have hmem : (p, q) ∈ reps n := mem_reps.mpr ⟨hp, hq, hpq⟩
  have hcard : 0 < (reps n).card := Finset.card_pos.mpr ⟨(p, q), hmem⟩
  have : (0 : ℝ) < ((reps n).card : ℝ) := by exact_mod_cast hcard
  simpa [spectralCount] using this

/--
A *spectral model* for the Goldbach problem: an analytic surrogate `main` for the
representation count, agreeing with the true spectral count up to an error term `err`
which is dominated by the main term for all even `n` beyond a threshold `N₀`.

This packages the (genuinely open) analytic input.  Everything else in this file is
unconditional.
-/
structure SpectralModel where
  /-- The spectral main term. -/
  main : ℕ → ℝ
  /-- The spectral error term. -/
  err : ℕ → ℝ
  /-- Threshold beyond which the model is claimed to be valid. -/
  N₀ : ℕ
  /-- The model reproduces the representation count exactly. -/
  decomposition : ∀ n : ℕ, spectralCount n = main n + err n
  /-- Beyond the threshold, the main term strictly dominates the error for even `n`. -/
  dominates : ∀ n : ℕ, N₀ ≤ n → Even n → |err n| < main n

/-- Above its threshold, a spectral model forces a positive representation count. -/
lemma SpectralModel.spectralCount_pos (M : SpectralModel) {n : ℕ}
    (hn : M.N₀ ≤ n) (hev : Even n) : 0 < spectralCount n := by
  have h := M.dominates n hn hev
  have h1 : -M.err n ≤ |M.err n| := neg_le_abs _
  have h2 := M.decomposition n
  linarith

/-- Above its threshold, a spectral model yields Goldbach representations. -/
lemma SpectralModel.goldbachPair (M : SpectralModel) {n : ℕ}
    (hn : M.N₀ ≤ n) (hev : Even n) : GoldbachPair n :=
  goldbachPair_of_spectralCount_pos (M.spectralCount_pos hn hev)

/-- The finitely many small even cases `4 ≤ n < N` of Goldbach's conjecture.  A conditional
version of the schema below would have to *assume* `SmallCases M.N₀`; we discharge it. -/
def SmallCases (N : ℕ) : Prop := ∀ n : ℕ, 4 ≤ n → n < N → Even n → GoldbachPair n

/-- **Discharge of the small-case hypothesis.**  Every even `n` with `4 ≤ n ≤ 100` is a sum of
two primes.  This is an unconditional finite verification. -/
lemma smallCases_101 : SmallCases 101 := by
  intro n h4 hlt hev
  obtain ⟨k, hk⟩ := hev
  have hk' : n = 2 * k := by omega
  subst hk'
  have hk1 : 2 ≤ k := by omega
  have hk2 : k ≤ 50 := by omega
  clear h4 hlt hk
  unfold GoldbachPair
  interval_cases k <;>
    first
      | exact ⟨2, 2, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 3, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 5, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 5, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 7, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 7, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 7, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 11, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 11, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 13, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 13, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 17, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 17, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 19, by norm_num, by norm_num, rfl⟩
      | exact ⟨11, 19, by norm_num, by norm_num, rfl⟩
      | exact ⟨13, 19, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨13, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨17, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 29, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨23, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨29, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨31, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨29, 37, by norm_num, by norm_num, rfl⟩
      | exact ⟨31, 37, by norm_num, by norm_num, rfl⟩
      | exact ⟨37, 37, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 41, by norm_num, by norm_num, rfl⟩
      | exact ⟨37, 41, by norm_num, by norm_num, rfl⟩
      | exact ⟨41, 41, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 43, by norm_num, by norm_num, rfl⟩
      | exact ⟨41, 43, by norm_num, by norm_num, rfl⟩
      | exact ⟨43, 43, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 47, by norm_num, by norm_num, rfl⟩
      | exact ⟨43, 47, by norm_num, by norm_num, rfl⟩
      | exact ⟨47, 47, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨47, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨53, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 61, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 67, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 67, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 73, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 73, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 79, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 83, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 89, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 89, by norm_num, by norm_num, rfl⟩

/-- Monotonicity of the small-case statement in the bound. -/
lemma smallCases_of_le {M N : ℕ} (hMN : M ≤ N) (h : SmallCases N) : SmallCases M :=
  fun n h4 hlt hev => h n h4 (lt_of_lt_of_le hlt hMN) hev

/--
**Goldbach from a spectral model.**

If a spectral model is valid from some threshold `N₀ ≤ 101` onwards, then *every* even
`n ≥ 4` is a sum of two primes.

The auxiliary hypothesis `SmallCases M.N₀`, covering the finite range `4 ≤ n < N₀` that the
model says nothing about, is **discharged unconditionally** here (see `smallCases_101`), so
the conclusion depends on nothing beyond the analytic input packaged in `M`.

The proof splits on whether `n` lies above or below the model's threshold and closes each
branch separately: above the threshold by positivity of the spectral count, below it by the
finite verification.
-/
theorem goldbach_from_spectral_model (M : SpectralModel) (hN₀ : M.N₀ ≤ 101) :
    ∀ n : ℕ, 4 ≤ n → Even n → GoldbachPair n := by
  intro n h4 hev
  by_cases hbig : M.N₀ ≤ n
  · exact M.goldbachPair hbig hev
  · exact smallCases_101 n h4 (by omega) hev

/-- The schema is not vacuous in the trivial direction either: Goldbach's conjecture itself
yields a spectral model (with zero error and threshold `4`). -/
noncomputable def spectralModelOfGoldbach
    (h : ∀ n : ℕ, 4 ≤ n → Even n → GoldbachPair n) : SpectralModel where
  main := spectralCount
  err := fun _ => 0
  N₀ := 4
  decomposition := fun n => by simp
  dominates := fun n hn hev => by
    simpa using spectralCount_pos_of_goldbachPair (h n hn hev)

end GoldbachSchema
end Brockian

