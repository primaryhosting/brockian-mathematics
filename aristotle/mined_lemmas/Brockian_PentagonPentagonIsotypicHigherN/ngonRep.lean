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

def ngonRep (n : ℕ) : Representation ℂ (DihedralGroup n) (ZMod n → ℂ) where
  toFun := ngonLin n
  map_one' := by
    ext f x
    show ngonAct n (DihedralGroup.r 0) f x = f x
    simp [ngonAct]
  map_mul' g h := by
    ext f x
    cases g with
    | r i => cases h with
      | r j => show f _ = f _; ring_nf
      | sr j => rw [DihedralGroup.r_mul_sr]; show f _ = f _; ring_nf
    | sr i => cases h with
      | r j => rw [DihedralGroup.sr_mul_r]; show f _ = f _; ring_nf
      | sr j => rw [DihedralGroup.sr_mul_sr]; show f _ = f _; ring_nf

