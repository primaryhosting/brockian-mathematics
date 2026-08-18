/-
  Brockian/Hypothesis/PrimePairsInAP.lean

  Explicit conjectural interfaces for prime-pair asymptotics in arithmetic
  progressions. These are `Prop` definitions, never typeclass instances and never
  silently supplied by imports.

  Important distinction:
    * `PrimePairsInAPAtModulus q g` is fixed-modulus only.
    * `UniformPrimePairsInAP g Q` has uniformity exactly for `q ≤ Q(X)`.

  Neither proposition is implied by Bombieri–Vinogradov. A downstream theorem must
  take the proposition it consumes as an explicit argument, for example

    theorem example (h : UniformPrimePairsInAP g Q) : ...

  This file is an interface specification until it receives V4/V5 evidence; it is
  intentionally not imported by the root build during the legacy-module migration.
-/
import Brockian.EquidistributionSchema

set_option autoImplicit false

open Filter Topology
open Brockian.Admissibility
open Brockian.Equidistribution

namespace Brockian.Hypothesis

/-- A function specifying the largest modulus admitted at a count bound `X`. -/
abbrev ModulusRange := ℕ → ℕ

/-- A concrete logarithmic-range family, using an integer base-two logarithm. It is
only a named range; no analytic assertion is encoded by this definition. -/
def logPowerRange (A : ℕ) : ModulusRange := fun X => (Nat.log 2 (X + 2)) ^ A

/-- Natural-number presentation of an admissible start class. The bounded representative
condition `a < q` is carried separately in uniform hypotheses. -/
def IsAdmissibleStart (q g a : ℕ) : Prop :=
  a % q ≠ 0 ∧ (a + g) % q ≠ 0

/-- **Fixed-modulus prime-pair asymptotic (OPEN).**

For this one modulus `q` and one gap `g`, the actual `configCount` is assumed to have
per-class main terms and lower-order errors. This does *not* assert any uniformity as
`q` varies. It is a `Prop`, so every conditional theorem must carry a witness
`h : PrimePairsInAPAtModulus q g` explicitly. -/
def PrimePairsInAPAtModulus (q : ℕ) [NeZero q] (g : ℕ) : Prop :=
  ∃ (sing : ZMod q → ℝ) (mainTerm : ℕ → ℝ) (err : ZMod q → ℕ → ℝ),
    (∀ a ∈ admissibleResidues q (g : ZMod q), 0 < sing a) ∧
    Tendsto mainTerm atTop atTop ∧
    (∀ a ∈ admissibleResidues q (g : ZMod q),
      Tendsto (fun X => err a X / mainTerm X) atTop (nhds 0)) ∧
    (g : ZMod q) ≠ 0 ∧
    (∀ a ∈ admissibleResidues q (g : ZMod q), ∀ X,
      |(configCount X q g a : ℝ) - sing a * mainTerm X| ≤ err a X)

/-- **Uniform prime-pair asymptotic in APs (OPEN).**

For a fixed gap `g`, the error is uniform over every modulus `q` in the *explicit*
range `3 ≤ q ≤ Q(X)`. The per-class constants are intentionally not required to agree:
equal singular-series factors are a separate analytic assertion. This proposition is
not implied by Bombieri–Vinogradov. Its mathematical strength changes when `Q` changes,
so downstream theorem statements must expose `Q` rather than hide a level of distribution. -/
def UniformPrimePairsInAP (g : ℕ) (Q : ModulusRange) : Prop :=
  ∃ (sing : ℕ → ℕ → ℝ) (mainTerm epsilon : ℕ → ℝ),
    Tendsto mainTerm atTop atTop ∧
    (∀ X, 0 ≤ epsilon X) ∧
    Tendsto epsilon atTop (nhds 0) ∧
    (∀ X q a, 3 ≤ q → q ≤ Q X → a < q → IsAdmissibleStart q g a →
      |(configCount X q g (a : ZMod q) : ℝ) - sing q a * mainTerm X|
        ≤ epsilon X * mainTerm X)

end Brockian.Hypothesis
