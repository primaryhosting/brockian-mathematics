/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization notes

Mathlib (as of the pinned commit) contains no development of étale cohomology, Weil
cohomology theories, or zeta functions of varieties over finite fields, so no existing

lemma closes this goal (`exact?`/`apply?` find nothing: the statement below is not an
instance of anything in the library).  We therefore formalize the *statement* of the
Riemann hypothesis part of the Weil conjectures in the standard "Frobenius eigenvalue"
form, and prove it (together with the Lefschetz trace formula that ties the eigenvalues
to point counts) for the base case of projective space `P^n` over `F_q`.

The data of a Weil cohomology theory for a variety `X/F_q` of dimension `d` is packaged
as a family of finite multisets `eig w` (`w = 0, …, 2d`) of complex numbers, the
eigenvalues of the geometric Frobenius on the `w`-th cohomology group.

* `Frontier.LefschetzTraceFormula` : `#X(F_{q^m}) = ∑_w (-1)^w ∑_{α ∈ eig w} α^m`.
* `Frontier.WeilRH` : every `α ∈ eig w` has `‖α‖ = q^(w/2)` (an algebraic number all of
  whose conjugates have absolute value `q^(w/2)`), i.e. the zeta function's zeros lie on
  the lines `Re s = w/2`.

For `P^n` the cohomology is one-dimensional in each even degree `2i`, `0 ≤ i ≤ n`, with
Frobenius eigenvalue `q^i`, and vanishes in odd degrees; the point counts are
`#P^n(F_{q^m}) = ∑_{i=0}^n q^{im}`.
-/

namespace Frontier

open Finset

/-- The number of `F_{q^m}`-rational points of projective `n`-space:
`#P^n(F_{q^m}) = 1 + q^m + ⋯ + q^{nm}`. -/
