import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
`i` and `j` are adjacent iff they differ by `1` modulo `10`. -/

lemma ee_ne_one {m : ZMod 10} (hm : m ≠ 0) : ee m ≠ 1 := by
  intro h
  apply hm
  have hlt : m.val < 10 := ZMod.val_lt m
  have hdvd := (zeta_prim.pow_eq_one_iff_dvd m.val).1 h
  have hz : m.val = 0 := by
    rcases Nat.eq_zero_or_pos m.val with h0 | h0
    · exact h0
    · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
  exact (ZMod.val_eq_zero m).1 hz

