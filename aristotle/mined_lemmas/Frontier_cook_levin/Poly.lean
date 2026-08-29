import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem Poly.mul {f g : ℕ → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun n => f n * g n) := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun n => ?_⟩
  calc f n * g n ≤ (c1 * (n + 1) ^ d1) * (c2 * (n + 1) ^ d2) := Nat.mul_le_mul (h1 n) (h2 n)
    _ = c1 * c2 * (n + 1) ^ (d1 + d2) := by ring

end Frontier

import Mathlib
import RequestProject.NP

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## NP-hardness of SAT

Given a verifier for `L`, the reduction maps an input word `x` of length `n` to the
bit string encoding the Tseitin CNF of the verifying circuit `C n`, in which the input
variables are fixed to the bits of `x` and the witness variables are left free.

Every bit of the produced string is a constant or a bit of `x` or its negation, i.e.
the reduction is a *projection*.
-/

namespace Frontier

open Std.Sat

/-- A bit string transformation which is computed bit-by-bit from single bits of the
input word, with polynomially many output bits. -/
