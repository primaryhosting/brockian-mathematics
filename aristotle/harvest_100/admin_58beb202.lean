/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the spin–statistics connection for a relativistic quantum field in the
Wightman framework, at the level of the two–point function, and proves it from the standard
axiomatic inputs.

## Setup

* `Frontier.Minkowski` is `ℝ^{1,3}` with quadratic form `Frontier.minkowskiSq` of signature
  `(+,-,-,-)`; two events are spacelike separated when the interval between them is negative.
* Test functions are complex valued functions on Minkowski space; two of them are *causally
  disjoint* (`Frontier.SpacelikeSupported`) when every point of the support of the first is
  spacelike separated from every point of the support of the second.
* A `Frontier.WightmanField` packages a Hilbert space with a vacuum vector, smeared field
  operators `op f`, a spin (recorded through `twoSpin`, twice the spin, so that integer spin
  means `twoSpin` even) and a choice of statistics (`fermionic`), together with three of the
  Wightman axioms that are used here:
  - hermiticity of the smeared field,
  - the (graded) local commutation relation at spacelike separation, with the sign dictated by
    the chosen statistics,
  - *weak locality*: at spacelike separation the two point function is symmetric up to the sign
    `(-1)^{2j}` dictated by the spin.  This is the Bargmann–Hall–Wightman consequence of Lorentz
    covariance, the spectral condition and the existence of Jost points.

## Results

* `Frontier.twoPoint_eq_zero_of_wrong_statistics`: if the statistics sign disagrees with the
  spin sign, the two point function vanishes for all causally disjoint test functions.
* `Frontier.op_vac_eq_zero_of_wrong_statistics`: adding the Reeh–Schlieder / edge–of–the–wedge
  input (a two point function vanishing on an open set of spacelike configurations vanishes
  identically) the field annihilates the vacuum, i.e. the theory is trivial.
* `Frontier.spin_statistics`: the spin–statistics connection.  A field that does not annihilate
  the vacuum must have statistics matching its spin: Bose statistics for integer spin, Fermi
  statistics for half–integer spin.
-/

namespace Frontier

open scoped InnerProductSpace

/-! ## Minkowski space and causal disjointness -/

/-- Minkowski spacetime `ℝ^{1,3}`, coordinates indexed by `Fin 4` with `0` the time coordinate. -/
abbrev Minkowski := Fin 4 → ℝ

/-- The Minkowski quadratic form, in signature `(+,-,-,-)`. -/
def minkowskiSq (x : Minkowski) : ℝ := x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2

/-- Two events of Minkowski space are spacelike separated when the interval between them is
negative. -/
def SpacelikeSep (x y : Minkowski) : Prop := minkowskiSq (x - y) < 0

/-- No event is spacelike separated from itself. -/
lemma not_spacelikeSep_self (x : Minkowski) : ¬ SpacelikeSep x x := by
  simp [SpacelikeSep, minkowskiSq]

/-- Complex valued test functions on Minkowski space. -/
abbrev TestFn := Minkowski → ℂ

/-- Complex conjugate of a test function. -/
def TestFn.conj (f : TestFn) : TestFn := fun x => (starRingEnd ℂ) (f x)

/-- Two test functions are causally disjoint when their supports are mutually spacelike
separated. -/
def SpacelikeSupported (f g : TestFn) : Prop :=
  ∀ x ∈ Function.support f, ∀ y ∈ Function.support g, SpacelikeSep x y

/-! ## Signs -/

/-- The statistics sign: `-1` for fermionic (anticommuting) fields, `+1` for bosonic
(commuting) fields. -/
def statSign (fermionic : Bool) : ℂ := if fermionic then -1 else 1

/-- The spin sign `(-1)^{2j}`: `+1` for integer spin, `-1` for half-integer spin. -/
def spinSign (twoSpin : ℕ) : ℂ := (-1) ^ twoSpin

lemma statSign_eq_one_or (b : Bool) : statSign b = 1 ∨ statSign b = -1 := by
  cases b <;> simp [statSign]

lemma spinSign_eq_one_or (n : ℕ) : spinSign n = 1 ∨ spinSign n = -1 := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl (h.neg_one_pow)
  · exact Or.inr (h.neg_one_pow)

/-- Two signs that differ are opposite. -/
lemma eq_neg_of_sign_ne {a b : ℂ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hab : a ≠ b) :
    a = -b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-! ## Wightman fields -/

/-- A (scalar-smeared) relativistic quantum field in the Wightman framework, carrying a spin and
a choice of statistics, together with the axioms needed for the spin–statistics connection.

`twoSpin` is twice the spin of the field, so integer spin corresponds to `twoSpin` even and
half-integer spin to `twoSpin` odd. -/
structure WightmanField (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vacuum vector. -/
  vac : H
  /-- The smeared field operator `φ(f)`. -/
  op : TestFn → (H →ₗ[ℂ] H)
  /-- Twice the spin of the field. -/
  twoSpin : ℕ
  /-- Whether the field is quantised with anticommutators. -/
  fermionic : Bool
  /-- Hermiticity of the smeared field: `φ(f)† = φ(f̄)`. -/
  herm : ∀ (f : TestFn) (x y : H), inner ℂ (op f x) y = inner ℂ x (op f.conj y)
  /-- Local (anti)commutation relations: at spacelike separation the fields commute or
  anticommute according to the chosen statistics. -/
  locality : ∀ (f g : TestFn), SpacelikeSupported f g →
    ∀ x : H, op f (op g x) = statSign fermionic • op g (op f x)
  /-- Weak locality: the Bargmann–Hall–Wightman consequence of Lorentz covariance and the
  spectral condition, stating that at spacelike separation the two point function is symmetric
  up to the sign `(-1)^{2j}`. -/
  weakLocality : ∀ (f g : TestFn), SpacelikeSupported f g →
    inner ℂ vac (op f (op g vac)) = spinSign twoSpin * inner ℂ vac (op g (op f vac))

namespace WightmanField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two point Wightman function `W(f, g) = ⟨Ω, φ(f) φ(g) Ω⟩`. -/
def twoPoint (F : WightmanField H) (f g : TestFn) : ℂ :=
  inner ℂ F.vac (F.op f (F.op g F.vac))

/-- The local (anti)commutation relation, read on the two point function. -/
lemma twoPoint_locality (F : WightmanField H) {f g : TestFn} (h : SpacelikeSupported f g) :
    F.twoPoint f g = statSign F.fermionic * F.twoPoint g f := by
  unfold twoPoint
  rw [F.locality f g h F.vac, inner_smul_right]

/-- Weak locality, read on the two point function. -/
lemma twoPoint_weakLocality (F : WightmanField H) {f g : TestFn} (h : SpacelikeSupported f g) :
    F.twoPoint f g = spinSign F.twoSpin * F.twoPoint g f :=
  F.weakLocality f g h

/-- The squared norm of `φ(f) Ω` is the two point function `W(f̄, f)`. -/
lemma normSq_op_vac (F : WightmanField H) (f : TestFn) :
    inner ℂ (F.op f F.vac) (F.op f F.vac) = F.twoPoint f.conj f := by
  rw [F.herm f F.vac (F.op f F.vac)]
  rfl

end WightmanField

/-! ## The spin–statistics connection -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Wrong statistics kill the two point function at spacelike separation.**

If the statistics sign of the field disagrees with the sign `(-1)^{2j}` dictated by its spin,
then the local (anti)commutation relations and weak locality force the two point function to
vanish for all causally disjoint test functions. -/
theorem twoPoint_eq_zero_of_wrong_statistics (F : WightmanField H)
    (hmis : statSign F.fermionic ≠ spinSign F.twoSpin)
    {f g : TestFn} (h : SpacelikeSupported f g) : F.twoPoint f g = 0 := by
  have hneg : statSign F.fermionic = -spinSign F.twoSpin :=
    eq_neg_of_sign_ne (statSign_eq_one_or _) (spinSign_eq_one_or _) hmis
  have h1 : F.twoPoint f g = statSign F.fermionic * F.twoPoint g f := F.twoPoint_locality h
  have h2 : F.twoPoint f g = spinSign F.twoSpin * F.twoPoint g f := F.twoPoint_weakLocality h
  have h3 : (2 : ℂ) * F.twoPoint f g = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h1]
    nth_rewrite 1 [h2]
    rw [hneg]
    ring
  simpa using h3

/-- **Wrong statistics make the theory trivial.**

Adding to the Wightman axioms the Reeh–Schlieder / edge-of-the-wedge input `hRS` — a two point
function vanishing for all causally disjoint test functions vanishes identically — a field whose
statistics disagree with its spin annihilates the vacuum. -/
theorem op_vac_eq_zero_of_wrong_statistics (F : WightmanField H)
    (hRS : (∀ f g : TestFn, SpacelikeSupported f g → F.twoPoint f g = 0) →
      ∀ f g : TestFn, F.twoPoint f g = 0)
    (hmis : statSign F.fermionic ≠ spinSign F.twoSpin) (f : TestFn) :
    F.op f F.vac = 0 := by
  have hall : ∀ f g : TestFn, F.twoPoint f g = 0 := by
    refine hRS ?_
    intro f g h
    exact twoPoint_eq_zero_of_wrong_statistics F hmis h
  have : inner ℂ (F.op f F.vac) (F.op f F.vac) = (0 : ℂ) := by
    rw [F.normSq_op_vac f]; exact hall _ _
  exact inner_self_eq_zero.mp this

/-- **The spin–statistics connection.**

Let `F` be a relativistic quantum field in the Wightman framework: hermitian smeared fields,
graded local commutation relations at spacelike separation with the sign given by its statistics,
and weak locality with the sign `(-1)^{2j}` given by its spin.  Assume the Reeh–Schlieder /
edge-of-the-wedge input `hRS`, and that the field is nontrivial, i.e. it does not annihilate the
vacuum.  Then its statistics are determined by its spin:
`(-1)^{2j} = +1` (integer spin) forces Bose statistics, and `(-1)^{2j} = -1` (half-integer spin)
forces Fermi statistics. -/
theorem spin_statistics (F : WightmanField H)
    (hRS : (∀ f g : TestFn, SpacelikeSupported f g → F.twoPoint f g = 0) →
      ∀ f g : TestFn, F.twoPoint f g = 0)
    (hnontrivial : ∃ f : TestFn, F.op f F.vac ≠ 0) :
    statSign F.fermionic = spinSign F.twoSpin := by
  by_contra hmis
  obtain ⟨f, hf⟩ := hnontrivial
  exact hf (op_vac_eq_zero_of_wrong_statistics F hRS hmis f)

/-- Spelt out for integer spin: a nontrivial field of integer spin is bosonic. -/
theorem bose_of_integer_spin (F : WightmanField H)
    (hRS : (∀ f g : TestFn, SpacelikeSupported f g → F.twoPoint f g = 0) →
      ∀ f g : TestFn, F.twoPoint f g = 0)
    (hnontrivial : ∃ f : TestFn, F.op f F.vac ≠ 0) (hspin : Even F.twoSpin) :
    F.fermionic = false := by
  have h := spin_statistics F hRS hnontrivial
  have hs : spinSign F.twoSpin = (1 : ℂ) := hspin.neg_one_pow (α := ℂ)
  rw [hs] at h
  cases hb : F.fermionic
  · rfl
  · rw [hb] at h; norm_num [statSign] at h

/-- Spelt out for half-integer spin: a nontrivial field of half-integer spin is fermionic. -/
theorem fermi_of_half_integer_spin (F : WightmanField H)
    (hRS : (∀ f g : TestFn, SpacelikeSupported f g → F.twoPoint f g = 0) →
      ∀ f g : TestFn, F.twoPoint f g = 0)
    (hnontrivial : ∃ f : TestFn, F.op f F.vac ≠ 0) (hspin : Odd F.twoSpin) :
    F.fermionic = true := by
  have h := spin_statistics F hRS hnontrivial
  have hs : spinSign F.twoSpin = (-1 : ℂ) := hspin.neg_one_pow (α := ℂ)
  rw [hs] at h
  cases hb : F.fermionic
  · rw [hb] at h; norm_num [statSign] at h
  · rfl

/-! ## Consistency of the axiom system

The Wightman axioms recorded in `Frontier.WightmanField` are consistent: the trivial field on a
one dimensional Hilbert space satisfies all of them (with any spin and either statistics).  Of
course it annihilates the vacuum, so it does not contradict the theorem above. -/

/-- The trivial field, for any spin and either statistics. -/
noncomputable def trivialField (n : ℕ) (b : Bool) : WightmanField ℂ where
  vac := 1
  op _ := 0
  twoSpin := n
  fermionic := b
  herm := by intro f x y; simp
  locality := by intro f g _ x; simp
  weakLocality := by intro f g _; simp

/-! ### A nontrivial model

The hypotheses of `Frontier.spin_statistics` are jointly satisfiable: there is a bosonic field of
spin `0` which does not annihilate the vacuum and for which the Reeh–Schlieder input holds.  So
the theorem is not vacuous. -/

/-- The origin of Minkowski space. -/
def origin : Minkowski := fun _ => 0

/-- A point at unit spatial distance from the origin, at equal time. -/
def unitSpace : Minkowski := fun i => if i = 1 then 1 else 0

lemma origin_ne_unitSpace : origin ≠ unitSpace := by
  intro h
  have := congrFun h 1
  simp [origin, unitSpace] at this

lemma spacelikeSep_origin_unitSpace : SpacelikeSep origin unitSpace := by
  have h : minkowskiSq (origin - unitSpace) = -1 := by
    simp [minkowskiSq, origin, unitSpace, Pi.sub_apply, show (0 : Fin 4) ≠ 1 by decide,
      show (2 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 1 by decide]
  rw [SpacelikeSep, h]
  norm_num

/-- A bosonic spin `0` field on a one dimensional Hilbert space, given by multiplication by
`f(origin) + f(unitSpace)`.  It is local (all its operators commute) and nontrivial. -/
noncomputable def pointPairField : WightmanField ℂ where
  vac := 1
  op f := (f origin + f unitSpace) • LinearMap.id
  twoSpin := 0
  fermionic := false
  herm := by
    intro f x y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, RCLike.inner_apply, TestFn.conj,
      map_add, map_mul, smul_eq_mul]
    ring
  locality := by
    intro f g _ x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, statSign, smul_eq_mul,
      Bool.false_eq_true, if_false, one_mul]
    ring
  weakLocality := by
    intro f g _
    simp only [LinearMap.smul_apply, LinearMap.id_apply, spinSign, pow_zero, one_mul,
      RCLike.inner_apply, smul_eq_mul]
    ring

/-- The field `pointPairField` does not annihilate the vacuum. -/
lemma pointPairField_nontrivial : ∃ f : TestFn, pointPairField.op f pointPairField.vac ≠ 0 := by
  refine ⟨fun _ => 1, ?_⟩
  simp [pointPairField]

/-- Its two point function does not vanish on all causally disjoint pairs, so the
Reeh–Schlieder implication holds for it. -/
lemma pointPairField_reehSchlieder :
    (∀ f g : TestFn, SpacelikeSupported f g → pointPairField.twoPoint f g = 0) →
      ∀ f g : TestFn, pointPairField.twoPoint f g = 0 := by
  classical
  intro h f g
  exfalso
  set a : TestFn := fun x => if x = origin then 1 else 0 with ha
  set b : TestFn := fun x => if x = unitSpace then 1 else 0 with hb
  have hsupp : SpacelikeSupported a b := by
    intro x hx y hy
    have hx' : x = origin := by
      by_contra hne
      exact hx (by simp [ha, hne])
    have hy' : y = unitSpace := by
      by_contra hne
      exact hy (by simp [hb, hne])
    subst hx'; subst hy'
    exact spacelikeSep_origin_unitSpace
  have := h a b hsupp
  rw [WightmanField.twoPoint] at this
  simp [pointPairField, ha, hb, origin_ne_unitSpace, Ne.symm origin_ne_unitSpace] at this

/-- Applying the spin–statistics theorem to the nontrivial model: it is indeed bosonic. -/
example : statSign pointPairField.fermionic = spinSign pointPairField.twoSpin :=
  spin_statistics pointPairField pointPairField_reehSchlieder pointPairField_nontrivial

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

