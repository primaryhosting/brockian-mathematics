/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

def ngonLin (n : ℕ) (g : DihedralGroup n) : (ZMod n → ℂ) →ₗ[ℂ] (ZMod n → ℂ) where
  toFun := ngonAct n g
  map_add' _ _ := by cases g <;> rfl
  map_smul' _ _ := by cases g <;> rfl

/-- The vertex representation of the dihedral group `D_n` on `ZMod n → ℂ`. -/
