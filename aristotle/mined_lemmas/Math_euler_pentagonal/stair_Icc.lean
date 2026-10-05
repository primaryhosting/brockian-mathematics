import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma stair_Icc {a b : ℕ} (h : a ≤ b) (ha : 1 ≤ a) : stair (Finset.Icc a b) = b + 1 - a := by
  have hmx : mx (Finset.Icc a b) = b := mx_Icc h
  refine le_antisymm (stair_le ?_) (le_stair (zero_notMem_Icc ha) ?_)
  · rw [hmx]
    intro hmem
    rw [Finset.mem_Icc] at hmem
    omega
  · intro i hi
    rw [hmx, Finset.mem_Icc]
    omega

/-- If `S` is not exceptional and we are in the first Franklin case, the move is legal. -/
