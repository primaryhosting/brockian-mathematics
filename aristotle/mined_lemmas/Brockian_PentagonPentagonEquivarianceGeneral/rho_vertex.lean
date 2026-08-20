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

lemma rho_vertex {n : ℕ} (hn : n ≠ 0) (g : DihedralGroup n) (k : ZMod n) :
    rho n g (vertex n k) = vertex n (act n g k) := by
  haveI : NeZero n := ⟨hn⟩
  cases g with
  | r i =>
    show zpowRoot n (i.val : ℤ) * zpowRoot n (k.val : ℤ) = zpowRoot n (((i + k).val : ℤ))
    rw [← zpowRoot_add]
    exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)
  | sr i =>
    show zpowRoot n (-(i.val : ℤ)) * (starRingEnd ℂ) (zpowRoot n (k.val : ℤ))
        = zpowRoot n (((-i - k).val : ℤ))
    rw [conj_zpowRoot, ← zpowRoot_add]
    exact zpowRoot_congr hn (by push_cast [natCast_val_self]; ring)

/-- The `n` vertices of the regular `n`-gon are pairwise distinct. -/
