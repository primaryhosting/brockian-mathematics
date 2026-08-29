/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma huckel_C8_eigenvector (k : ℕ) (hk : k < 8) :
    C8adj.mulVec (fun j => om ((k : ZMod 8) * j))
      = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) : ℝ) : ℂ) • fun j => om ((k : ZMod 8) * j) := by
  have hval : ((k : ZMod 8)).val = k := ZMod.val_natCast_of_lt hk
  have hlam : ((2 * Real.cos (2 * Real.pi * (k : ℝ) / 8) : ℝ) : ℂ)
      = om (k : ZMod 8) + om (-(k : ZMod 8)) := by
    rw [om_add_om_neg, hval]
  funext j
  rw [C8adj_mulVec]
  have e1 : (k : ZMod 8) * (j + 1) = (k : ZMod 8) * j + (k : ZMod 8) := by ring
  have e2 : (k : ZMod 8) * (j - 1) = (k : ZMod 8) * j + (-(k : ZMod 8)) := by ring
  simp only [e1, e2, om_add, Pi.smul_apply, smul_eq_mul, hlam]
  ring

/-- Any eigenvalue of the adjacency matrix of `C₈` is a root of `x(x² - 2)(x² - 4)`. -/
