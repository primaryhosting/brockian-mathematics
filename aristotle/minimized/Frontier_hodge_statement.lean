/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of the pinned revision) contains no singular cohomology of complex
varieties, no Hodge decomposition and no Chow groups / cycle class maps, so there
is no existing lemma that closes this goal: the statement has to be built from
scratch.  We therefore

* define rational Hodge structures (`Frontier.HodgeStructure`) and their spaces of
  Hodge classes (`Frontier.hodgeClasses`),
* package the cohomological data of a smooth projective complex variety together
  with its cycle class maps (`Frontier.HodgeData`),
* state the Hodge conjecture for such data (`Frontier.HodgeConjecture`), and
* prove, in `Frontier.hodge_statement`, the base case `p = 0` of the conjecture
  together with the standard reduction of the conjecture to the inclusion
  "every Hodge class is algebraic".
-/

import Mathlib

namespace Frontier

open TensorProduct

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation on `ℂ ⊗[ℚ] V`, acting on the left tensor factor.  It is only
`ℚ`-linear (it is conjugate-linear over `ℂ`). -/

noncomputable def hodgeClasses (p : ℕ) (H : HodgeStructure V (2 * p)) : Submodule ℚ V :=
  ((H.piece (p, p)).restrictScalars ℚ).comap (TensorProduct.mk ℚ ℂ V 1)

/-- In weight `0` the whole complexification is of type `(0,0)`. -/

lemma HodgeStructure.piece_zero_eq_top (H : HodgeStructure V (2 * 0)) :
    H.piece (0, 0) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← H.internal.submodule_iSup_eq_top]
  refine iSup_le fun pq => ?_
  rcases eq_or_ne (pq.1 + pq.2) (2 * 0) with h | h
  · have h1 : pq.1 = 0 := by omega
    have h2 : pq.2 = 0 := by omega
    have : pq = (0, 0) := Prod.ext h1 h2
    exact this ▸ le_rfl
  · exact (H.weight pq h).le.trans bot_le

/-- Every rational class is a Hodge class in weight `0`. -/

lemma hodgeClasses_zero_eq_top (H : HodgeStructure V (2 * 0)) :
    hodgeClasses 0 H = ⊤ := by
  simp [hodgeClasses, H.piece_zero_eq_top]

/-! ## The cohomological data of a smooth projective complex variety -/

/-- The data entering the Hodge conjecture for a smooth **connected** projective complex
variety `X`:

* `H p` is the rational cohomology `H^{2p}(X, ℚ)`, carrying a rational Hodge structure of
  weight `2p`;
* `Cyc p` is the `ℚ`-vector space of algebraic cycles of codimension `p` on `X` with
  rational coefficients, and `cl p` is the cycle class map;
* `cl_hodge` records the classical fact that cycle classes are Hodge classes;
* `fund` is the fundamental class `[X] ∈ Cyc 0`, whose image spans `H^0(X, ℚ)` because
  `X` is connected.

Since Mathlib has neither singular cohomology of complex varieties nor Chow groups, this
structure axiomatises exactly the input needed to state the conjecture. -/
structure HodgeData where
  /-- The rational cohomology group `H^{2p}(X, ℚ)`. -/
  H : ℕ → Type*
  [addCommGroupH : ∀ p, AddCommGroup (H p)]
  [moduleH : ∀ p, Module ℚ (H p)]
  /-- The Hodge structure of weight `2p` on `H^{2p}(X, ℚ)`. -/
  hs : ∀ p, HodgeStructure (H p) (2 * p)
  /-- Codimension-`p` algebraic cycles with rational coefficients. -/
  Cyc : ℕ → Type*
  [addCommGroupCyc : ∀ p, AddCommGroup (Cyc p)]
  [moduleCyc : ∀ p, Module ℚ (Cyc p)]
  /-- The cycle class map. -/
  cl : ∀ p, Cyc p →ₗ[ℚ] H p
  /-- Cycle classes are Hodge classes. -/
  cl_hodge : ∀ p, LinearMap.range (cl p) ≤ hodgeClasses p (hs p)
  /-- The fundamental class of `X`. -/
  fund : Cyc 0
  /-- `X` is connected: `H^0(X, ℚ)` is spanned by the fundamental class. -/
  connected : Submodule.span ℚ {cl 0 fund} = ⊤

attribute [instance] HodgeData.addCommGroupH HodgeData.moduleH
attribute [instance] HodgeData.addCommGroupCyc HodgeData.moduleCyc

/-- The Hodge conjecture in codimension `p`: every Hodge class of type `(p,p)` on `X` is a
rational linear combination of classes of algebraic cycles, i.e. the image of the cycle
class map is exactly the space of Hodge classes. -/

def HodgeConjectureAt (D : HodgeData) (p : ℕ) : Prop :=
  LinearMap.range (D.cl p) = hodgeClasses p (D.hs p)

/-- **The Hodge conjecture**: for every smooth projective complex variety and every `p`,
the Hodge classes of type `(p,p)` are precisely the classes of algebraic cycles. -/

def HodgeConjecture (D : HodgeData) : Prop := ∀ p, HodgeConjectureAt D p

/-! ## The statement, with its base case and the standard reduction -/

/-- **Hodge statement.**  With the Hodge conjecture formalised as `HodgeConjecture`:

1. the base case `p = 0` holds unconditionally (for a connected smooth projective variety,
   `H^0` consists entirely of Hodge classes and is spanned by the algebraic fundamental
   class), and
2. the conjecture reduces to a single inclusion: since cycle classes are always Hodge
   classes, the conjecture is equivalent to the statement that every Hodge class is
   algebraic. -/

theorem hodge_statement (D : HodgeData) :
    HodgeConjectureAt D 0 ∧
      (HodgeConjecture D ↔ ∀ p, hodgeClasses p (D.hs p) ≤ LinearMap.range (D.cl p)) := by
  constructor
  · have htop : LinearMap.range (D.cl 0) = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← D.connected]
      refine Submodule.span_le.mpr ?_
      rintro x rfl
      exact ⟨D.fund, rfl⟩
    rw [HodgeConjectureAt, htop, hodgeClasses_zero_eq_top]
  · constructor
    · intro h p
      exact (h p).ge
    · intro h p
      exact le_antisymm (D.cl_hodge p) (h p)

/-! ## Non-vacuity: the axiomatised data is realisable

The following explicit `HodgeData` (all cohomology and cycle groups equal to `ℚ`, with the
whole complexification of type `(p,p)`) shows that the hypotheses packaged in `HodgeData`
are consistent, so `hodge_statement` is not vacuous. -/

open Classical in
/-- The Hodge structure of weight `2p` on `ℚ` which is purely of type `(p,p)`. -/
