/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/
def doubleHom (A : Type*) [AddCommGroup A] : A →+ A :=
  AddMonoidHom.mk' (fun a => (2 : ℕ) • a) (by intro a b; simp [smul_add])

@[simp]
lemma doubleHom_apply {A : Type*} [AddCommGroup A] (a : A) :
    doubleHom A a = (2 : ℕ) • a := rfl

/-- The axioms satisfied by a (naive or canonical) Weil height `h` on an abelian group `A`:

* `translate`: for every `Q`, the height of `P + Q` is at most `2 * h P` up to a constant
  depending only on `Q`;
* `double`: the height of `2 • P` is at least `4 * h P` up to a constant;
* `finite_le`: only finitely many points have bounded height.

These are exactly the properties of the naive height on the rational points of an elliptic
curve over `ℚ` that are used in the descent step of the Mordell–Weil theorem. -/
structure IsWeilHeight (A : Type*) [AddCommGroup A] (h : A → ℝ) : Prop where
  translate : ∀ Q : A, ∃ C : ℝ, ∀ P : A, h (P + Q) ≤ 2 * h P + C
  double : ∃ C : ℝ, ∀ P : A, 4 * h P ≤ h ((2 : ℕ) • P) + C
  finite_le : ∀ C : ℝ, {P : A | h P ≤ C}.Finite

variable {A : Type*} [AddCommGroup A]

/-- **Descent theorem.** An abelian group carrying a Weil height and having finite quotient
`A / 2A` is finitely generated. This is the group-theoretic heart of the Mordell–Weil
theorem: it turns the *weak* Mordell–Weil theorem (finiteness of `A / 2A`) into full finite
generation. -/
theorem fg_of_isWeilHeight_of_finite_quotient (h : A → ℝ) (hh : IsWeilHeight A h)
    (hq : Finite (A ⧸ (doubleHom A).range)) : AddGroup.FG A := by
  classical
  set K := (doubleHom A).range with hK
  set rep : (A ⧸ K) → A := fun c => Quotient.out c with hrepdef
  have htr : ∀ c : A ⧸ K, ∃ C : ℝ, ∀ P : A, h (P + (-(rep c))) ≤ 2 * h P + C :=
    fun c => hh.translate _
  choose Cf hCf using htr
  obtain ⟨C, hC⟩ := Finite.exists_le Cf
  obtain ⟨D, hD⟩ := hh.double
  set B : ℝ := (C + D) / 2 with hB
  set S : Set A := Set.range rep ∪ {P | h P ≤ B} with hS
  have hSfin : S.Finite := (Set.finite_range rep).union (hh.finite_le B)
  set G := AddSubgroup.closure S with hG
  have hsub : ∀ x ∈ S, x ∈ G := fun x hx => AddSubgroup.subset_closure hx
  -- The key descent step: any point outside `G` admits a point outside `G` of smaller height.
  have key : ∀ P : A, P ∉ G → ∃ P' : A, P' ∉ G ∧ h P' < h P := by
    intro P hP
    have hPB : B < h P := by
      by_contra hle
      push_neg at hle
      exact hP (hsub P (Or.inr hle))
    set c : A ⧸ K := QuotientAddGroup.mk P with hc
    have hrepc : (QuotientAddGroup.mk (rep c) : A ⧸ K) = c := QuotientAddGroup.out_eq' c
    have hmem : P - rep c ∈ K := by
      rw [← QuotientAddGroup.eq_zero_iff]
      rw [QuotientAddGroup.mk_sub, hrepc, hc]
      simp
    obtain ⟨P', hP'⟩ := hmem
    have hPeq : P = (2 : ℕ) • P' + rep c := by
      have : (2 : ℕ) • P' = P - rep c := hP'
      rw [this]; abel
    have h1 : h ((2 : ℕ) • P') ≤ 2 * h P + C := by
      have : (2 : ℕ) • P' = P + (-(rep c)) := by
        rw [show ((2 : ℕ) • P' : A) = P - rep c from hP']; abel
      calc h ((2 : ℕ) • P') = h (P + (-(rep c))) := by rw [this]
        _ ≤ 2 * h P + Cf c := hCf c P
        _ ≤ 2 * h P + C := by linarith [hC c]
    have h2 : 4 * h P' ≤ h ((2 : ℕ) • P') + D := hD P'
    have h3 : h P' < h P := by
      have : B < h P := hPB
      rw [hB] at this
      linarith
    refine ⟨P', ?_, h3⟩
    intro hP'G
    apply hP
    have hrepG : rep c ∈ G := hsub _ (Or.inl ⟨c, rfl⟩)
    rw [hPeq]
    exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hP'G 2) hrepG
  -- Minimal counterexample argument.
  have htop : G = ⊤ := by
    by_contra hne
    obtain ⟨P, hP⟩ : ∃ P : A, P ∉ G := by
      by_contra hall
      push_neg at hall
      exact hne (eq_top_iff.mpr fun x _ => hall x)
    have hXfin : {R : A | R ∉ G ∧ h R ≤ h P}.Finite :=
      (hh.finite_le (h P)).subset (fun x hx => hx.2)
    have hXne : hXfin.toFinset.Nonempty := ⟨P, by simp [hXfin.mem_toFinset, hP]⟩
    obtain ⟨R, hRmem, hmin⟩ := hXfin.toFinset.exists_min_image h hXne
    rw [hXfin.mem_toFinset] at hRmem
    obtain ⟨R', hR'G, hR'lt⟩ := key R hRmem.1
    have : R' ∈ hXfin.toFinset := by
      rw [hXfin.mem_toFinset]
      exact ⟨hR'G, le_of_lt (lt_of_lt_of_le hR'lt hRmem.2)⟩
    exact absurd (hmin R' this) (not_le.mpr hR'lt)
  exact AddGroup.fg_iff.mpr ⟨S, htop, hSfin⟩

/-- Sanity check that the hypotheses of the descent theorem are satisfiable and not vacuous:
on a finite abelian group the zero function is a Weil height and the quotient by `2A` is
finite, so the descent theorem indeed yields finite generation. -/
theorem isWeilHeight_zero_of_finite [Finite A] : IsWeilHeight A (fun _ => 0) where
  translate := fun _ => ⟨0, by intro P; norm_num⟩
  double := ⟨0, by intro P; norm_num⟩
  finite_le := fun _ => Set.toFinite _

/-- A nontrivial instantiation of the descent theorem: the squared absolute value is a Weil
height on `ℤ`. -/
theorem isWeilHeight_int_sq : IsWeilHeight ℤ (fun n => ((n : ℝ)) ^ 2) where
  translate := fun Q => ⟨2 * ((Q : ℝ)) ^ 2, by
    intro P
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) - (Q : ℝ))]⟩
  double := ⟨0, by
    intro P
    have : (((2 : ℕ) • P : ℤ) : ℝ) = 2 * (P : ℝ) := by simp
    rw [this]
    nlinarith [sq_nonneg ((P : ℝ))]⟩
  finite_le := by
    intro C
    apply Set.Finite.subset (Set.finite_Icc (-(max ⌈C⌉ 1)) (max ⌈C⌉ 1))
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have habs : ((|n| : ℤ) : ℝ) = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
    have h1 : |n| ≤ ⌈C⌉ ∨ |n| ≤ 1 := by
      rcases le_or_gt |(n : ℝ)| 1 with h | h
      · right
        have : ((|n| : ℤ) : ℝ) ≤ 1 := by rw [habs]; exact h
        exact_mod_cast this
      · left
        have hle : ((|n| : ℤ) : ℝ) ≤ C := by
          rw [habs]
          nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)]
        have : ((|n| : ℤ) : ℝ) ≤ (⌈C⌉ : ℝ) := le_trans hle (Int.le_ceil C)
        exact_mod_cast this
    simp only [Set.mem_Icc]
    rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases h1 with h1 | h1 <;>
      simp only [le_max_iff] <;> omega

lemma finite_int_quotient_two : Finite (ℤ ⧸ (doubleHom ℤ).range) := by
  apply Finite.of_surjective (fun (i : Fin 2) => (QuotientAddGroup.mk (i : ℤ) :
    ℤ ⧸ (doubleHom ℤ).range))
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H n =>
    rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨0, by rw [QuotientAddGroup.eq]; exact ⟨m, by simp [doubleHom]; omega⟩⟩
    · exact ⟨1, by rw [QuotientAddGroup.eq]; exact ⟨m, by simp [doubleHom]; omega⟩⟩

/-- The descent theorem applied to `ℤ`, showing that its hypotheses are satisfiable by an
infinite group. -/
example : AddGroup.FG ℤ :=
  fg_of_isWeilHeight_of_finite_quotient _ isWeilHeight_int_sq finite_int_quotient_two

/-- The group of rational points of an elliptic curve over `ℚ`, in Weierstrass form. -/
abbrev RationalPoints (W : WeierstrassCurve ℚ) : Type := W.toAffine.Point

/-- The Mordell–Weil statement: for every elliptic curve over `ℚ`, the group of its rational
points is finitely generated. -/
def MordellWeilStatement : Prop :=
  ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic], AddGroup.FG (RationalPoints W)

/-- **Mordell's theorem, as a Lean-checked reduction.**

Assume:

* (canonical/naive height machinery) every elliptic curve over `ℚ` carries a height function
  on its group of rational points satisfying the Weil height axioms `IsWeilHeight`, and
* (weak Mordell–Weil) for every elliptic curve over `ℚ` the quotient `E(ℚ) / 2 E(ℚ)` is finite.

Then the group of rational points of every elliptic curve over `ℚ` is finitely generated. -/
theorem Mordell_finite_generation
    (hheight : ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic],
      ∃ h : RationalPoints W → ℝ, IsWeilHeight (RationalPoints W) h)
    (hweak : ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic],
      Finite (RationalPoints W ⧸ (doubleHom (RationalPoints W)).range)) :
    MordellWeilStatement := by
  intro W _
  obtain ⟨h, hh⟩ := hheight W
  exact fg_of_isWeilHeight_of_finite_quotient h hh (hweak W)

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

