/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We generalize the `D₅` (regular pentagon) representation picture to arbitrary regular
`n`-gons.  Concretely, for `n ≠ 0` we build

* `Brockian.zpowRoot n m = exp (2πi·m/n)`, the `n`-th roots of unity indexed by `ℤ`;
* `Brockian.vertex n k`, the vertices of the regular `n`-gon, indexed by `ZMod n`;
* `Brockian.rho n`, the standard two dimensional real representation of
  `DihedralGroup n` realized on `ℂ` (rotations act by multiplication by a root of unity,
  reflections by a root of unity times complex conjugation);
* `Brockian.act n`, the combinatorial action of `DihedralGroup n` on the vertex labels
  `ZMod n`.

The main theorem `Brockian.PentagonPentagonEquivarianceGeneral` states that `rho` is a
representation, that `act` is an action, and that the vertex map
`vertex n : ZMod n → ℂ` is an injective equivariant map between them.  Specializing to
`n = 5` recovers the pentagon statement (`Brockian.pentagon_equivariance`).
-/

namespace Brockian

open Complex

section Aux

/-- `((a.val : ℕ) : ZMod n) = a`. -/

lemma vertex_eq_zpowRoot {n : ℕ} (hn : n ≠ 0) (m : ℤ) :
    vertex n ((m : ZMod n)) = zpowRoot n m := by
  haveI : NeZero n := ⟨hn⟩
  exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)

/-- The standard representation of `DihedralGroup n` on `ℂ ≅ ℝ²`: the rotation `r i` acts
by multiplication by `exp (2πi·i/n)`, and the reflection `sr i` acts by conjugation
followed by multiplication by `exp (-2πi·i/n)`. -/
