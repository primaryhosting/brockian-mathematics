import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/

lemma exists_hybrid_gap {m : ℕ} (hm : 0 < m) (p : ℕ → ℝ) (ε : ℝ)
    (h : ε < p m - p 0) : ∃ k, k < m ∧ ε / m < p (k + 1) - p k := by
  by_contra hc
  push_neg at hc
  have hsum : p m - p 0 = ∑ k ∈ range m, (p (k + 1) - p k) := (Finset.sum_range_sub p m).symm
  have hle : ∑ k ∈ range m, (p (k + 1) - p k) ≤ ∑ _k ∈ range m, ε / m :=
    Finset.sum_le_sum (fun k hk => hc k (Finset.mem_range.1 hk))
  rw [Finset.sum_const, card_range, nsmul_eq_mul] at hle
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have : (m : ℝ) * (ε / m) = ε := by field_simp
  rw [this] at hle
  linarith [hsum ▸ hle]

section NW

variable {n l m : ℕ}

/-- The Nisan–Wigderson generator built from a family of index maps `S` and a function `f`:
its `j`-th output bit is `f` applied to the seed `x` restricted along `S j`. -/
