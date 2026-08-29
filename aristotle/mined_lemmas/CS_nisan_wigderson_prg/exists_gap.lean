import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

open Finset

variable {n m : ℕ}

/-- The real value of a boolean: `1` for `true`, `0` for `false`. -/

lemma exists_gap (d : ℕ → ℝ) (M : ℕ) (hM : 0 < M) (ε : ℝ)
    (hε : ε ≤ |∑ k ∈ Finset.range M, d k|) : ∃ k < M, ε / M ≤ |d k| := by
  by_contra hcon
  push_neg at hcon
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h1 : |∑ k ∈ Finset.range M, d k| ≤ ∑ k ∈ Finset.range M, |d k| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ k ∈ Finset.range M, |d k| < ∑ _k ∈ Finset.range M, ε / M := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hM.ne')
    intro k hk
    exact hcon k (Finset.mem_range.mp hk)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_div_cancel₀ _ (ne_of_gt hMR)] at h2
  linarith

/-!
### The Nisan–Wigderson theorem

`f i` is a family of functions, each depending only on the seed bits in the set `S i`
(in the Nisan–Wigderson construction the `S i` form a combinatorial design, and `f i` is a hard
function evaluated on the corresponding subset of seed bits).  `nwGen f` is the associated
generator.  The theorem below is the "hardness from distinguishing" core of the
Nisan–Wigderson argument: if some test `T` distinguishes the output of the generator from the
uniform distribution with advantage `ε`, then, for some index `i`, the Nisan–Wigderson predictor
built from `T` computes `f i` correctly with probability at least `1/2 + ε/m`; moreover this
predictor reads only the seed bits in `S i`.  In other words, the generator can only be broken
if the hard function is not hard.
-/
