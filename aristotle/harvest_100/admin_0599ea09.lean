/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Cardinal FirstOrder Language

/-! ## Part 1: the statement of the Continuum Hypothesis

We state CH in two equivalent ways and prove the equivalence inside Lean:

* the *cardinal-arithmetic* form `2 ^ ℵ₀ = ℵ₁` (equivalently `𝔠 = ℵ₁`), and
* the *no intermediate cardinality* form: every set of reals which is uncountable
  has the cardinality of the continuum.
-/

/-- The Continuum Hypothesis, in cardinal-arithmetic form: `𝔠 = ℵ₁`. -/
def CH : Prop := (𝔠 : Cardinal.{0}) = ℵ₁

/-- The Continuum Hypothesis, in "no intermediate cardinality" form: every uncountable set
of reals is equinumerous with `ℝ`. -/
def CHNoIntermediate : Prop := ∀ s : Set ℝ, ℵ₀ < #s → #s = 𝔠

/-- `ℵ₁ ≤ 𝔠`: there is no set of reals of cardinality strictly between `ℵ₀` and `ℵ₁`.
This is a ZFC theorem (the "base case" of the independence discussion): CH can only fail
by `𝔠` being *larger* than `ℵ₁`. -/
theorem aleph_one_le_continuum : (ℵ₁ : Cardinal.{0}) ≤ 𝔠 :=
  Cardinal.aleph_one_le_continuum

/-- Cantor's theorem in the relevant instance: `ℵ₀ < 2 ^ ℵ₀ = 𝔠`. -/
theorem aleph0_lt_continuum : (ℵ₀ : Cardinal.{0}) < 𝔠 :=
  Cardinal.aleph0_lt_continuum

/-- The two formulations of CH agree. -/
theorem CH_iff_CHNoIntermediate : CH ↔ CHNoIntermediate := by
  constructor
  · intro h s hs
    have h1 : (ℵ₁ : Cardinal.{0}) ≤ #s := by
      rw [← Cardinal.succ_aleph0]
      exact Order.succ_le_of_lt hs
    have h2 : #s ≤ 𝔠 := by
      have : #s ≤ #ℝ := Cardinal.mk_set_le s
      rwa [Cardinal.mk_real] at this
    exact le_antisymm h2 (h ▸ h1)
  · intro h
    obtain ⟨s, hs⟩ : ∃ s : Set ℝ, #s = ℵ₁ := by
      rw [← Cardinal.le_mk_iff_exists_set, Cardinal.mk_real]
      exact aleph_one_le_continuum
    have hlt : ℵ₀ < #s := by
      rw [hs]
      exact Cardinal.aleph0_lt_aleph_one
    have := h s hlt
    rw [hs] at this
    exact this.symm

/-- CH is equivalent to the cardinal exponentiation statement `2 ^ ℵ₀ = ℵ₁`. -/
theorem CH_iff_two_pow_aleph0 : CH ↔ (2 : Cardinal.{0}) ^ (ℵ₀ : Cardinal.{0}) = ℵ₁ := by
  rw [CH, Cardinal.two_power_aleph0]

/-! ## Part 2: what independence means, and the Gödel/Cohen reduction

Lean cannot itself decide the provability of a sentence of ZFC — `Prop` here is Lean's
own logic, not ZFC's — so "CH is independent of ZFC" is formalized in the standard way,
as a statement about a first-order theory `T` and a sentence `φ` of its language:
neither `φ` nor `¬ φ` is a consequence of `T`.

The theorem below is the Lean-checked *reduction*: independence follows from the two
relative-consistency results,

* Gödel (1938): `ZFC + CH` has a model (the constructible universe `L`);
* Cohen (1963): `ZFC + ¬CH` has a model (a forcing extension),

each expressed as satisfiability of the corresponding extension of `T`.
-/

/-- `φ` is independent of the theory `T`: neither `φ` nor its negation is entailed by `T`. -/
def IndependentOf {L : Language} (T : L.Theory) (φ : L.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ φ.not

/-- **Independence from two consistency results.** If both `T ∪ {φ}` and `T ∪ {¬ φ}` are
satisfiable, then `φ` is independent of `T`. Applied with `T = ZFC` and `φ = CH`, the two
hypotheses are exactly Gödel's and Cohen's relative consistency theorems, and the
conclusion is the independence of the Continuum Hypothesis. -/
theorem independentOf_of_isSatisfiable {L : Language} {T : L.Theory} {φ : L.Sentence}
    (hCon : (T ∪ {φ}).IsSatisfiable) (hConNot : (T ∪ {φ.not}).IsSatisfiable) :
    IndependentOf T φ := by
  refine ⟨?_, ?_⟩
  · rw [Theory.models_iff_not_satisfiable]
    exact fun h => h hConNot
  · intro h
    obtain ⟨M⟩ := hCon
    haveI : (M : Type _) ⊨ T := M.is_model.mono Set.subset_union_left
    have hφ : (M : Type _) ⊨ φ := by
      have : φ ∈ T ∪ {φ} := Set.mem_union_right _ rfl
      exact M.is_model.realize_of_mem φ this
    have hnot : (M : Type _) ⊨ φ.not :=
      h.realize_sentence M
    rw [Sentence.realize_not] at hnot
    exact hnot hφ

/-! ## Main statement -/

/-- **The Continuum Hypothesis: statement and independence reduction.**

The three components are:

1. the two standard formulations of CH — `𝔠 = ℵ₁` and "no set of reals has cardinality
   strictly between `ℵ₀` and `𝔠`" — are equivalent, and both are equivalent to
   `2 ^ ℵ₀ = ℵ₁`;
2. the ZFC base facts `ℵ₀ < 𝔠` (Cantor) and `ℵ₁ ≤ 𝔠`, so CH is exactly the assertion
   that this second inequality is an equality;
3. the Gödel–Cohen reduction: for any first-order theory `T` and sentence `φ`,
   satisfiability of `T ∪ {φ}` (Gödel, via the constructible universe) together with
   satisfiability of `T ∪ {¬ φ}` (Cohen, via forcing) implies that `φ` is independent
   of `T`, i.e. neither `φ` nor `¬ φ` is a semantic consequence of `T`.

Statements 1 and 2 are proved outright; statement 3 is the Lean-checked reduction of
independence to the two relative consistency theorems, which are metamathematical facts
about ZFC and cannot be stated inside Lean's own logic without a formalization of the
ZFC proof system. -/
theorem CH_independent_statement :
    ((CH ↔ CHNoIntermediate) ∧ (CH ↔ (2 : Cardinal.{0}) ^ (ℵ₀ : Cardinal.{0}) = ℵ₁)) ∧
      ((ℵ₀ : Cardinal.{0}) < 𝔠 ∧ (ℵ₁ : Cardinal.{0}) ≤ 𝔠) ∧
      ∀ {L : Language} {T : L.Theory} {φ : L.Sentence},
        (T ∪ {φ}).IsSatisfiable → (T ∪ {φ.not}).IsSatisfiable → IndependentOf T φ :=
  ⟨⟨CH_iff_CHNoIntermediate, CH_iff_two_pow_aleph0⟩,
    ⟨aleph0_lt_continuum, aleph_one_le_continuum⟩,
    fun h1 h2 => independentOf_of_isSatisfiable h1 h2⟩

end Frontier

import Mathlib

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

