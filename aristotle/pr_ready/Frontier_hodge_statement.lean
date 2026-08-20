/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Statement: State the Hodge conjecture on algebraicity of Hodge classes.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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


namespace Frontier

open TensorProduct

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation on `ℂ ⊗[ℚ] V`, acting on the left tensor factor.  It is only
`ℚ`-linear (it is conjugate-linear over `ℂ`). -/
noncomputable def cxConj (V : Type*) [AddCommGroup V] [Module ℚ V] :
    (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  TensorProduct.map ((Complex.conjAe.toLinearMap).restrictScalars ℚ) LinearMap.id

@[simp] lemma cxConj_tmul (V : Type*) [AddCommGroup V] [Module ℚ V] (z : ℂ) (v : V) :
    cxConj V (z ⊗ₜ[ℚ] v) = (starRingEnd ℂ) z ⊗ₜ[ℚ] v := rfl

/-! ## Rational Hodge structures -/

/-- A rational Hodge structure of weight `n` on a `ℚ`-vector space `V`: a decomposition
of the complexification `ℂ ⊗[ℚ] V` into complex subspaces `V^{p,q}` with `p + q = n`,
which is exchanged by complex conjugation, `conj (V^{p,q}) = V^{q,p}`. -/
structure HodgeStructure (V : Type*) [AddCommGroup V] [Module ℚ V] (n : ℕ) where
  /-- The `(p,q)`-piece of the Hodge decomposition of the complexification. -/
  piece : ℕ × ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Only bidegrees of total degree `n` occur. -/
  weight : ∀ pq : ℕ × ℕ, pq.1 + pq.2 ≠ n → piece pq = ⊥
  /-- The pieces decompose the complexification as an internal direct sum. -/
  internal : DirectSum.IsInternal piece
  /-- Complex conjugation exchanges the `(p,q)`- and `(q,p)`-pieces. -/
  conj_piece : ∀ pq : ℕ × ℕ, Submodule.map (cxConj V) ((piece pq).restrictScalars ℚ)
      ≤ (piece (pq.2, pq.1)).restrictScalars ℚ

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The space of Hodge classes of type `(p,p)` in a rational Hodge structure of weight
`2p`: the rational classes whose image in the complexification lies in `V^{p,p}`. -/
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
noncomputable def trivialHodgeStructure (p : ℕ) : HodgeStructure ℚ (2 * p) where
  piece pq := if pq = (p, p) then ⊤ else ⊥
  weight pq hpq := by
    have : pq ≠ (p, p) := by
      rintro rfl
      exact hpq (by omega)
    simp [this]
  internal := by
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = (p, p)
      · subst hi
        have : (⨆ j, ⨆ (_ : j ≠ (p, p)),
            (if j = (p, p) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥)) = ⊥ :=
          iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => by simp [hj]
        rw [this]
        exact disjoint_bot_right
      · simp only [hi, if_false]
        exact disjoint_bot_left
    · exact top_le_iff.mp (le_iSup_of_le (p, p) (by simp))
  conj_piece pq := by
    by_cases hpq : pq = (p, p)
    · subst hpq
      simp
    · simp [hpq]

open Classical in
/-- An explicit example of `HodgeData`, witnessing that the structure is inhabited. -/
noncomputable def trivialHodgeData : HodgeData where
  H _ := ℚ
  hs p := trivialHodgeStructure p
  Cyc _ := ℚ
  cl _ := LinearMap.id
  cl_hodge p := by
    have : hodgeClasses p (trivialHodgeStructure p) = ⊤ := by
      simp [hodgeClasses, trivialHodgeStructure]
    rw [this]
    exact le_top
  fund := 1
  connected := by
    simp

end Frontier


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

