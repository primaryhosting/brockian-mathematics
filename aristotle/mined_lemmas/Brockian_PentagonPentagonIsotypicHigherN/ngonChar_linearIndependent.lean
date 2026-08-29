import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/

lemma ngonChar_linearIndependent (j : ZMod n) (hj : j ≠ -j) :
    LinearIndependent ℂ ![⇑(ngonChar n j), ⇑(ngonChar n (-j))] := by
  have hinj : Function.Injective ![ngonChar n j, ngonChar n (-j)] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [ngonChar_ne j hj, (ngonChar_ne j hj).symm]
  have := (AddChar.linearIndependent (ZMod n) ℂ).comp _ hinj
  have hfun : (DFunLike.coe ∘ ![ngonChar n j, ngonChar n (-j)])
      = ![⇑(ngonChar n j), ⇑(ngonChar n (-j))] := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at this

/-- The isotypic component is two-dimensional when `j ≠ -j`. -/
