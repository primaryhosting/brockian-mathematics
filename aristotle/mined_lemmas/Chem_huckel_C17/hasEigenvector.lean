/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma hasEigenvector (k : ZMod 17) :
    C17adj *ᵥ (fun j => ee (k * j)) = lam k • (fun j => ee (k * j)) := by
  funext i
  rw [mulVec_C17adj]
  have h1 : k * (i - 1) = k * i + -k := by ring
  have h2 : k * (i + 1) = k * i + k := by ring
  rw [h1, h2, ee_add, ee_add]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ee_add_ee_neg k]
  ring

