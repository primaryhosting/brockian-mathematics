/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-! ## The multiplication-by-`m` subgroup and its quotient -/

/-- Multiplication by `m` as an endomorphism of an additive commutative group. -/
def nsmulHom (m : ℕ) (A : Type*) [AddCommGroup A] : A →+ A :=
  AddMonoidHom.mk' (fun a => m • a) (fun a b => smul_add m a b)

@[simp]
lemma nsmulHom_apply (m : ℕ) {A : Type*} [AddCommGroup A] (a : A) :
    nsmulHom m A a = m • a := rfl

/-- The subgroup `mA = { m • a | a ∈ A }` of an additive commutative group `A`. -/
def smulSubgroup (m : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (nsmulHom m A).range

lemma mem_smulSubgroup {m : ℕ} {A : Type*} [AddCommGroup A] {a : A} :
    a ∈ smulSubgroup m A ↔ ∃ b : A, m • b = a := Iff.rfl

/-- If `A / H` is finite, then there is a finite set of coset representatives for `H` in `A`. -/
lemma exists_finset_reps {A : Type*} [AddCommGroup A] (H : AddSubgroup A)
    [Finite (A ⧸ H)] : ∃ S : Finset A, ∀ P : A, ∃ Q ∈ S, P - Q ∈ H := by
  classical
  have : Fintype (A ⧸ H) := Fintype.ofFinite _
  refine ⟨Finset.image (fun q : A ⧸ H => Quotient.out q) Finset.univ, fun P => ?_⟩
  refine ⟨Quotient.out (QuotientAddGroup.mk' H P), Finset.mem_image_of_mem _ (Finset.mem_univ _),
    ?_⟩
  have h1 : (QuotientAddGroup.mk' H) (Quotient.out (QuotientAddGroup.mk' H P))
      = (QuotientAddGroup.mk' H) P := by
    simp
  have h2 := (QuotientAddGroup.eq (s := H)).mp h1
  simpa [sub_eq_add_neg, add_comm] using h2

/-! ## The abstract descent theorem

This is the group-theoretic engine behind the Mordell–Weil theorem
(the "descent theorem", Silverman, *The Arithmetic of Elliptic Curves*, VIII.3.1):
an abelian group carrying a height function with the standard properties and with
`A/mA` finite is finitely generated. -/

/-- **Descent theorem.** Let `A` be an abelian group, `m ≥ 2`, and `h : A → ℝ` a function
("height") such that

* `H1`: for every `Q` there is a constant `C` with `h (P + Q) ≤ 2 * h P + C` for all `P`;
* `H2`: there is a constant `C` with `m ^ 2 * h P ≤ h (m • P) + C` for all `P`;
* `H3`: for every `C` the set `{P | h P ≤ C}` is finite;

and such that `A / mA` is finite.  Then `A` is finitely generated. -/
theorem descent_theorem {A : Type*} [AddCommGroup A] (m : ℕ) (hm : 2 ≤ m) (h : A → ℝ)
    (H1 : ∀ Q : A, ∃ C : ℝ, ∀ P : A, h (P + Q) ≤ 2 * h P + C)
    (H2 : ∃ C : ℝ, ∀ P : A, (m : ℝ) ^ 2 * h P ≤ h (m • P) + C)
    (H3 : ∀ C : ℝ, {P : A | h P ≤ C}.Finite)
    [Finite (A ⧸ smulSubgroup m A)] : AddGroup.FG A := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_reps (smulSubgroup m A)
  -- reformulate the coset representatives
  have hS' : ∀ P : A, ∃ Q ∈ S, ∃ P' : A, P = m • P' + Q := by
    intro P
    obtain ⟨Q, hQ, hmem⟩ := hS P
    obtain ⟨P', hP'⟩ := hmem
    exact ⟨Q, hQ, P', by rw [nsmulHom_apply] at hP'; rw [hP']; abel⟩
  -- a uniform constant for `H1` over the (finitely many) representatives
  obtain ⟨C₂, hC₂⟩ := H2
  set f : A → ℝ := fun Q => Classical.choose (H1 (-Q)) with hf
  have hfspec : ∀ Q : A, ∀ P : A, h (P + -Q) ≤ 2 * h P + f Q :=
    fun Q => Classical.choose_spec (H1 (-Q))
  set c₁ : ℝ := (insert (0 : ℝ) (S.image f)).max' ⟨0, Finset.mem_insert_self _ _⟩ with hc₁
  have hc₁le : ∀ Q ∈ S, f Q ≤ c₁ := by
    intro Q hQ
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hQ))
  set c : ℝ := c₁ + C₂ with hc
  -- the basic descent inequality
  have key : ∀ P : A, ∀ Q ∈ S, ∀ P' : A, P = m • P' + Q →
      (m : ℝ) ^ 2 * h P' ≤ 2 * h P + c := by
    intro P Q hQ P' hP'
    have h1 : (m : ℝ) ^ 2 * h P' ≤ h (m • P') + C₂ := hC₂ P'
    have h2 : m • P' = P + -Q := by rw [hP']; abel
    have h3 : h (P + -Q) ≤ 2 * h P + f Q := hfspec Q P
    have h4 : f Q ≤ c₁ := hc₁le Q hQ
    rw [h2] at h1
    linarith
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmsq : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by linarith
  set T : ℝ := c / ((m : ℝ) ^ 2 - 2) with hT
  -- the generating set
  set K : AddSubgroup A := AddSubgroup.closure ((S : Set A) ∪ {P : A | h P ≤ T}) with hK
  have hsmall : ∀ P : A, h P ≤ T → P ∈ K := by
    intro P hP
    exact AddSubgroup.subset_closure (Or.inr hP)
  have hSK : ∀ Q ∈ S, Q ∈ K := by
    intro Q hQ
    exact AddSubgroup.subset_closure (Or.inl hQ)
  have htop : K = ⊤ := by
    by_contra hne
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : A, P₀ ∉ K := by
      by_contra hall
      push_neg at hall
      exact hne (eq_top_iff.mpr fun x _ => hall x)
    set F : Set A := {x : A | x ∉ K ∧ h x ≤ h P₀} with hF
    have hFfin : F.Finite := (H3 (h P₀)).subset (fun x hx => hx.2)
    have hFne : F.Nonempty := ⟨P₀, hP₀, le_rfl⟩
    obtain ⟨x, hxF, hxmin⟩ := Set.exists_min_image F h hFfin hFne
    have hxK : x ∉ K := hxF.1
    have hxT : T < h x := by
      by_contra hle
      push_neg at hle
      exact hxK (hsmall x hle)
    obtain ⟨Q, hQ, x', hx'⟩ := hS' x
    have hx'K : x' ∉ K := by
      intro hmem
      apply hxK
      rw [hx']
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hmem _) (hSK Q hQ)
    have hkey : (m : ℝ) ^ 2 * h x' ≤ 2 * h x + c := key x Q hQ x' hx'
    have hcx : c < ((m : ℝ) ^ 2 - 2) * h x := by
      have hpos : (0 : ℝ) < (m : ℝ) ^ 2 - 2 := by linarith
      rw [hT, div_lt_iff₀ hpos] at hxT
      linarith
    have hlt : h x' < h x := by nlinarith
    have hx'F : x' ∈ F := ⟨hx'K, le_trans hlt.le hxF.2⟩
    exact absurd (hxmin x' hx'F) (not_le.mpr hlt)
  refine AddGroup.fg_iff.mpr ⟨(S : Set A) ∪ {P : A | h P ≤ T}, htop, ?_⟩
  exact (S.finite_toSet).union (H3 T)

/-! ## The Mordell–Weil theorem for elliptic curves over `ℚ` -/

/-- The full statement of the Mordell–Weil theorem over `ℚ`: for every elliptic curve `E`
over `ℚ`, the group `E(ℚ)` of rational points is finitely generated. -/
def MordellWeilStatement : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → AddGroup.FG E.toAffine.Point

/-- **Mordell's theorem, reduced to weak Mordell–Weil plus the theory of heights.**

Let `E` be an elliptic curve over `ℚ` and let `h` be a height function on the group `E(ℚ)`
of rational points satisfying the three standard properties of the (logarithmic) canonical
height:

* for each fixed `Q ∈ E(ℚ)` there is a constant `C` with `h (P + Q) ≤ 2 * h P + C`;
* there is a constant `C` with `4 * h P ≤ h (2 • P) + C`;
* for each `C`, only finitely many points have height at most `C` (Northcott property).

If moreover the weak Mordell–Weil group `E(ℚ)/2E(ℚ)` is finite, then `E(ℚ)` is a
finitely generated abelian group.

(The hypothesis that `E` is elliptic is kept for faithfulness to the statement; the argument
itself only uses the group structure on the set of nonsingular rational points.) -/
theorem Mordell_finite_generation (E : WeierstrassCurve ℚ) (_hE : E.IsElliptic)
    (h : E.toAffine.Point → ℝ)
    (H1 : ∀ Q : E.toAffine.Point, ∃ C : ℝ, ∀ P : E.toAffine.Point, h (P + Q) ≤ 2 * h P + C)
    (H2 : ∃ C : ℝ, ∀ P : E.toAffine.Point, 4 * h P ≤ h (2 • P) + C)
    (H3 : ∀ C : ℝ, {P : E.toAffine.Point | h P ≤ C}.Finite)
    [Finite (E.toAffine.Point ⧸ smulSubgroup 2 E.toAffine.Point)] :
    AddGroup.FG E.toAffine.Point := by
  refine descent_theorem 2 le_rfl h H1 ?_ H3
  obtain ⟨C, hC⟩ := H2
  refine ⟨C, fun P => ?_⟩
  have := hC P
  norm_num
  linarith

/-- The full Mordell–Weil statement over `ℚ` follows from the existence, for every elliptic
curve over `ℚ`, of a height function with the three standard properties together with
finiteness of the weak Mordell–Weil group `E(ℚ)/2E(ℚ)`. -/
theorem MordellWeilStatement_of_height_of_weak
    (H : ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ∃ h : E.toAffine.Point → ℝ,
        (∀ Q : E.toAffine.Point, ∃ C : ℝ, ∀ P : E.toAffine.Point, h (P + Q) ≤ 2 * h P + C) ∧
        (∃ C : ℝ, ∀ P : E.toAffine.Point, 4 * h P ≤ h (2 • P) + C) ∧
        (∀ C : ℝ, {P : E.toAffine.Point | h P ≤ C}.Finite) ∧
        Finite (E.toAffine.Point ⧸ smulSubgroup 2 E.toAffine.Point)) :
    MordellWeilStatement := by
  intro E hE
  obtain ⟨h, H1, H2, H3, hfin⟩ := H E hE
  exact @Mordell_finite_generation E hE h H1 H2 H3 hfin

/-- Base case: if the group of rational points is finite, it is finitely generated. -/
theorem Mordell_finite_generation_of_finite (E : WeierstrassCurve ℚ)
    [Finite E.toAffine.Point] : AddGroup.FG E.toAffine.Point :=
  AddGroup.fg_iff.mpr ⟨Set.univ, by simp, Set.finite_univ⟩

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

