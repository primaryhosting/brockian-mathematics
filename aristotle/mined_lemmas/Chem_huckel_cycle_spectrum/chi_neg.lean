/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

lemma chi_neg (n : ℕ) [NeZero n] (a : ZMod n) : chi n (-a) = (chi n a)⁻¹ := by
  have h : chi n a * chi n (-a) = 1 := by rw [← chi_add]; simp [chi_zero]
  have ha := chi_ne_zero n a
  field_simp
  linear_combination h

