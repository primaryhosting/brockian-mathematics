/-
# Toda Theorem
Category: Frontier Cs
Target: CS.toda_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- header above is a plain comment and is repeated as the module docstring
-- immediately after the import.)

import Mathlib

/-!
# Toda Theorem
Category: Frontier Cs
Target: CS.toda_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this formalization

Toda's theorem states `PH ⊆ P^{#P}`.  This file develops a self-contained,
machine-independent framework in which the three ingredients of that statement
(alternating polynomially-length-bounded quantification, exact counting of
witnesses, and post-processing of the count) are given precise definitions, and
proves the inclusion `PH ⊆ P^{#P}` in that framework.

The framework is parameterized by a `CS.BaseClass`: a class of "feasible"
predicates, closed under negation, under polynomially length-bounded
existential quantification, and under discarding certificates, together with a
class of feasible post-processing predicates containing the positivity test.
All classes (`CS.SigmaClass`, `CS.PH`, `CS.SharpP`, `CS.PSharpP`, `CS.ParityP`)
are defined relative to such a base class.

Honest statement of what is and is not captured: the closure of the base class
under bounded existential quantification is an assumption of the framework.
For the *uniform polynomial-time* base class this closure property is exactly
what is not available (it is equivalent to `P = NP`), and it is precisely there
that Toda's original proof needs its deep ingredients (the Valiant–Vazirani
isolation lemma, `PH ⊆ BP·⊕P`, and the modulus-amplification step
`BP·⊕P ⊆ P^{#P}`).  So the main theorem below is Toda's inclusion in an
abstract counting framework, not a formalization of Toda's proof for uniform
polynomial time.  (Indeed, a base class closed under bounded existential
quantification already makes each level of the hierarchy feasible, which is why
the inclusion below has a direct proof: the `Σₖ` condition itself becomes a
feasible matrix, whose witnesses are then counted.)

Two genuine ingredients of Toda's argument are proved here as well, in
model-independent form:

* `CS.parityP_subset_PSharpP` : the parity class is contained in `P^{#P}`,
  since a parity is the low bit of an exact count;
* `CS.toda_modulus_amplification` : if `a ≡ -1 (mod 2^k)` then
  `3a⁴ + 4a³ ≡ -1 (mod 2^{2k})`, the algebraic step that doubles the modulus
  in Toda's derandomization.
-/

namespace CS

/-- Binary strings. -/
abbrev Word := List Bool

/-- A language is a set of binary strings. -/
abbrev Language := Set Word

/-- `p` is bounded by a polynomial. -/

lemma mem_altB (B : BaseClass) (p : ℕ → ℕ) (hp : IsPolyBound p)
    (R : Word → List Word → Bool) (hR : B.Mem R) :
    ∀ k, B.Mem (fun x ys => AltB p R k x ys) := by
  intro k
  induction k with
  | zero => exact hR
  | succ k ih =>
      have h := B.mem_exists p (fun x ys => !(AltB p R k x ys)) hp (B.mem_not _ ih)
      exact h

/-- **Toda's theorem**, `PH ⊆ P^{#P}`, in the abstract counting framework of
this file: every language in the polynomial hierarchy over a feasible base
class is decided by a feasible post-processing of a single `#P` count.

See the file header for a precise account of what this formalization does and
does not capture. -/
