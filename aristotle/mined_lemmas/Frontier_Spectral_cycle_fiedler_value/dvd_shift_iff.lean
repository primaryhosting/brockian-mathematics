import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/

lemma dvd_shift_iff (hn : n ≠ 0) (j l : Fin n) :
    n ∣ (j.val + (n - 1) * l.val) ↔ j = l := by
  constructor
  · intro hdvd
    have hone : (1:ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hz : (n : ℤ) ∣ ((j.val : ℤ) - (l.val : ℤ)) := by
      obtain ⟨c, hc⟩ := hdvd
      have hcz : (j.val : ℤ) + ((n : ℤ) - 1) * (l.val : ℤ) = (n : ℤ) * c := by
        have hh := congrArg (fun t : ℕ => (t : ℤ)) hc
        push_cast [Nat.cast_sub hone] at hh
        linarith [hh]
      exact ⟨c - l.val, by linarith [hcz]⟩
    have hlt : |((j.val : ℤ) - (l.val : ℤ))| < (n : ℤ) := by
      have h1 := j.isLt
      have h2 := l.isLt
      rw [abs_lt]
      omega
    have := Int.eq_zero_of_abs_lt_dvd hz hlt
    have : (j.val : ℤ) = (l.val : ℤ) := by linarith
    exact Fin.val_inj.mp (by exact_mod_cast this)
  · rintro rfl
    refine ⟨j.val, ?_⟩
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    cases n with
    | zero => omega
    | succ p => simp; ring

