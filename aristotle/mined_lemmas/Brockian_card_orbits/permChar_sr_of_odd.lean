-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

open DihedralGroup

namespace Brockian

/-!
## Setup: the dihedral group acting on the vertices of a regular `n`-gon

We model the vertices of the regular `n`-gon by `ZMod n`.  The dihedral group
`DihedralGroup n` acts on them, with the rotation `r i` translating by `-i` and the
reflection `sr i` acting by `x ↦ i - x`.  (The signs are dictated by Mathlib's
multiplication convention `r i * r j = r (i + j)`, `r i * sr j = sr (j - i)`,
`sr i * r j = sr (i + j)`, `sr i * sr j = r (j - i)`.)
-/

/-- The underlying map of the action of `DihedralGroup n` on the vertex set `ZMod n`
of the regular `n`-gon. -/

lemma permChar_sr_of_odd (n : ℕ) [NeZero n] (hn : Odd n) (i : ZMod n) :
    permChar n (sr i) = 1 := by
  obtain ⟨c, hc⟩ := exists_two_inv_of_odd (n := n) hn
  rw [permChar, Fintype.card_eq_one_iff]
  refine ⟨⟨i * c, show i - i * c = i * c by linear_combination (-i) * hc⟩, ?_⟩
  rintro ⟨y, hy⟩
  have hy' : i - y = y := hy
  exact Subtype.ext (show y = i * c by linear_combination (-c) * hy' + (-y) * hc)

/-!
## Main result

For the pentagon (`n = 5`) the permutation representation of `D₅` on the five vertices
contains the trivial representation exactly once.  The theorem below extends this to every
regular `n`-gon: the multiplicity

  `⟨permChar, 1⟩ = (1 / |D_n|) * ∑_{g} permChar g`

of the trivial character in the vertex permutation character equals `1`, for all `n ≥ 1`.
-/

/-- **Pentagon Pentagon Character Multiplicity Ext.**  For every `n ≥ 1`, the multiplicity
of the trivial character inside the character of the permutation representation of the
dihedral group `DihedralGroup n` on the vertices of the regular `n`-gon equals `1`.  This
generalizes the pentagon (`n = 5`, the group `D₅`) case to all `n`-gons.  The proof is
Burnside's lemma, `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, together with
transitivity of the vertex action. -/
