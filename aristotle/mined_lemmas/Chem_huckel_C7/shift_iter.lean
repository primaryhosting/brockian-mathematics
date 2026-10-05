import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

lemma shift_iter {y : ℂ} {u : ZMod 7 → ℂ} (h : ∀ i, u (i + 1) = y * u i) (n : ℕ) (i : ZMod 7) :
    u (i + (n : ZMod 7)) = y ^ n * u i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (i + ((n + 1 : ℕ) : ZMod 7)) = (i + (n : ZMod 7)) + 1 := by push_cast; ring
      rw [hstep, h, ih, pow_succ]
      ring

/-- A nonzero eigenvector of the cyclic shift has eigenvalue a 7th root of unity. -/
