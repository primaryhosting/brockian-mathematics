/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- the required header text as a plain block comment, and is repeated as a module docstring below.)

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Finset ZMod AddChar

variable {n : ℕ} [NeZero n]

/-- The rotation of the regular `n`-gon acting on complex functions on its vertex set
`ZMod n`: `(rotateVertices f) j = f (j + 1)`. -/

lemma isoProj_isoProj (k l : ZMod n) (f : ZMod n → ℂ) :
    isoProj k (isoProj l f) = if k = l then isoProj l f else 0 := by
  by_cases h : k = l
  · subst h
    conv_lhs => rw [isoProj_eq_coeff_smul_charFun k f]
    rw [isoProj_smul, isoProj_charFun, if_pos rfl, if_pos rfl]
    exact (isoProj_eq_coeff_smul_charFun k f).symm
  · conv_lhs => rw [isoProj_eq_coeff_smul_charFun l f]
    rw [isoProj_smul, isoProj_charFun, if_neg h, if_neg h]
    funext j
    simp

/--
**Pentagon Pentagon Isotypic Higher N.**

The pentagon (`D₅`) isotypic decomposition generalizes to every regular `n`-gon: for
complex functions on the vertex set `ZMod n` of the regular `n`-gon, the operators
`isoProj k` form a complete family of mutually orthogonal idempotents (Fourier
inversion; idempotence/orthogonality), the image of `isoProj k` is the line spanned by
the rotation character `charFun k` (so `isoProj k f` is a rotation eigenvector with
eigenvalue `charFun k 1`), and the reflection of the dihedral group interchanges the
isotypic components of `k` and `-k`.
-/
