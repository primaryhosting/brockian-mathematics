/-
/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## The statement of the Mordell–Weil theorem

`Frontier.MordellStatement` is the formal statement of Mordell's theorem: for every elliptic
curve over `ℚ`, the group of rational points (in affine coordinates, i.e. the affine points
together with the point at infinity) is a finitely generated abelian group.

The main results below are a *Lean-checked reduction* of this statement to the two standard
inputs of the classical proof:

* the **weak Mordell–Weil theorem**: `E(ℚ)/2E(ℚ)` is finite, encoded as a finite set `R` of
  coset representatives;
* the **theory of heights**: a nonnegative height function `ht` on `E(ℚ)` with finite
  sublevel sets, a quasi-parallelogram bound `ht (P + Q) ≤ 2 * ht P + C_Q`, and a duplication
  bound `4 * ht P ≤ ht (2 • P) + C`.

The engine is `Frontier.descent_of_height`, the classical descent theorem for abstract abelian
groups, proved unconditionally below.
-/

/-- The Mordell–Weil theorem over `ℚ`: the group of rational points of an elliptic curve
over `ℚ` is finitely generated. -/
def MordellStatement : Prop :=
  ∀ (W : WeierstrassCurve ℚ), W.IsElliptic → AddGroup.FG W.toAffine.Point

/-!
## The descent theorem
-/

/-- **Descent theorem.** Let `A` be an abelian group equipped with a nonnegative "height"
function `ht` with finite sublevel sets, satisfying the quasi-parallelogram inequality
`ht (P + Q) ≤ 2 * ht P + C_Q` and the duplication inequality `m ^ 2 * ht P ≤ ht (m • P) + C`.
If `A / m • A` is finite (encoded by a finite set `R` of coset representatives), then `A` is
finitely generated. -/
theorem descent_of_height {A : Type*} [AddCommGroup A] {m : ℕ} (hm : 2 ≤ m)
    (ht : A → ℝ) (hnonneg : ∀ P : A, 0 ≤ ht P)
    (hfin : ∀ B : ℝ, {P : A | ht P ≤ B}.Finite)
    (htri : ∀ Q : A, ∃ C : ℝ, ∀ P : A, ht (P + Q) ≤ 2 * ht P + C)
    (hdup : ∃ C : ℝ, ∀ P : A, (m : ℝ) ^ 2 * ht P ≤ ht (m • P) + C)
    (R : Finset A) (hR : ∀ P : A, ∃ Q ∈ R, ∃ P' : A, P = m • P' + Q) :
    AddGroup.FG A := by
  classical
  obtain ⟨C, hC⟩ := hdup
  choose f hf using htri
  -- a uniform constant dominating all the constants `f (-Q)` for `Q ∈ R`
  set C₁ : ℝ := ∑ Q ∈ R, |f (-Q)| with hC₁
  have hC₁nonneg : 0 ≤ C₁ := Finset.sum_nonneg fun Q _ => abs_nonneg _
  have hC₁le : ∀ Q ∈ R, f (-Q) ≤ C₁ := by
    intro Q hQ
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun Q : A => |f (-Q)|)
      (fun _ _ => abs_nonneg _) hQ
  set E : ℝ := C₁ + |C| with hE
  have hEnonneg : 0 ≤ E := by positivity
  set D : ℝ := E / 4 with hD
  have hDnonneg : 0 ≤ D := by positivity
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- the key descent step
  have step : ∀ (P P₁ Q : A), Q ∈ R → P = m • P₁ + Q → ht P₁ ≤ ht P / 2 + D := by
    intro P P₁ Q hQ hPQ
    have h1 : (m : ℝ) ^ 2 * ht P₁ ≤ ht (m • P₁) + C := hC P₁
    have h4 : ht (m • P₁) = ht (P + -Q) := by
      rw [hPQ]; congr 1; abel
    have h5 : ht (P + -Q) ≤ 2 * ht P + f (-Q) := hf (-Q) P
    have h6 : f (-Q) ≤ C₁ := hC₁le Q hQ
    have h7 : C ≤ |C| := le_abs_self C
    have h8 : 0 ≤ ht P₁ := hnonneg P₁
    have h9 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have h10 : (4 : ℝ) * ht P₁ ≤ (m : ℝ) ^ 2 * ht P₁ := by nlinarith
    have : (4 : ℝ) * ht P₁ ≤ 2 * ht P + C₁ + |C| := by
      rw [h4] at h1
      linarith
    rw [hD, hE]
    linarith
  -- the finite generating set
  set T : Finset A := (hfin (4 * D + 4)).toFinset with hT
  set S : Finset A := R ∪ T with hS
  have hTmem : ∀ P : A, ht P ≤ 4 * D + 4 → P ∈ T := by
    intro P hP
    rw [hT, Set.Finite.mem_toFinset]
    exact hP
  have key : ∀ n : ℕ, ∀ P : A, ht P ≤ (n : ℝ) → P ∈ AddSubgroup.closure (S : Set A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro P hP
      by_cases hn : (n : ℝ) ≤ 4 * D + 4
      · refine AddSubgroup.subset_closure ?_
        have : P ∈ T := hTmem P (le_trans hP hn)
        simpa [hS] using Or.inr this
      · push_neg at hn
        obtain ⟨Q, hQR, P₁, rfl⟩ := hR P
        have hstep : ht P₁ ≤ ht (m • P₁ + Q) / 2 + D := step _ _ Q hQR rfl
        set n' : ℕ := ⌈(n : ℝ) / 2 + D⌉₊ with hn'
        have hpos : (0 : ℝ) ≤ (n : ℝ) / 2 + D := by positivity
        have hle : ht P₁ ≤ (n' : ℝ) := by
          have : (n : ℝ) / 2 + D ≤ (n' : ℝ) := Nat.le_ceil _
          linarith
        have hlt : n' < n := by
          have h1 : ((n' : ℝ)) < (n : ℝ) / 2 + D + 1 := Nat.ceil_lt_add_one hpos
          have : ((n' : ℝ)) < (n : ℝ) := by linarith
          exact_mod_cast this
        have hmem : P₁ ∈ AddSubgroup.closure (S : Set A) := IH n' hlt P₁ hle
        refine AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hmem m) ?_
        refine AddSubgroup.subset_closure ?_
        simpa [hS] using Or.inl hQR
  refine ⟨⟨S, ?_⟩⟩
  rw [AddSubgroup.eq_top_iff']
  intro P
  exact key ⌈ht P⌉₊ P (Nat.le_ceil _)

/-!
## The reduction of Mordell's theorem
-/

/-- **Mordell's theorem, reduced to weak Mordell–Weil and the theory of heights.**

Given an elliptic curve `W` over `ℚ`, assume:
* `ht` is a nonnegative height function on `W(ℚ)` whose sublevel sets are finite;
* `ht` satisfies the quasi-parallelogram bound `ht (P + Q) ≤ 2 * ht P + C_Q`;
* `ht` satisfies the duplication bound `4 * ht P ≤ ht (2 • P) + C`;
* `R` is a finite set of representatives for `W(ℚ) / 2 W(ℚ)` (weak Mordell–Weil).

Then `W(ℚ)` is a finitely generated abelian group. -/
theorem Mordell_finite_generation (W : WeierstrassCurve ℚ) (_hW : W.IsElliptic)
    (ht : W.toAffine.Point → ℝ)
    (hnonneg : ∀ P : W.toAffine.Point, 0 ≤ ht P)
    (hfin : ∀ B : ℝ, {P : W.toAffine.Point | ht P ≤ B}.Finite)
    (htri : ∀ Q : W.toAffine.Point, ∃ C : ℝ, ∀ P : W.toAffine.Point,
      ht (P + Q) ≤ 2 * ht P + C)
    (hdup : ∃ C : ℝ, ∀ P : W.toAffine.Point, 4 * ht P ≤ ht (2 • P) + C)
    (R : Finset W.toAffine.Point)
    (hR : ∀ P : W.toAffine.Point, ∃ Q ∈ R, ∃ P' : W.toAffine.Point, P = 2 • P' + Q) :
    AddGroup.FG W.toAffine.Point := by
  refine descent_of_height (m := 2) le_rfl ht hnonneg hfin htri ?_ R hR
  obtain ⟨C, hC⟩ := hdup
  refine ⟨C, fun P => ?_⟩
  have h2 : (((2 : ℕ) : ℝ)) ^ 2 = 4 := by norm_num
  rw [h2]
  exact hC P

/-- The Mordell–Weil theorem over `ℚ` follows from the existence, for every elliptic curve
over `ℚ`, of a height function with the standard properties together with the finiteness of
`E(ℚ)/2E(ℚ)`. -/
theorem MordellStatement_of_heights_and_weak_MordellWeil
    (H : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
      ∃ ht : W.toAffine.Point → ℝ,
        (∀ P : W.toAffine.Point, 0 ≤ ht P) ∧
        (∀ B : ℝ, {P : W.toAffine.Point | ht P ≤ B}.Finite) ∧
        (∀ Q : W.toAffine.Point, ∃ C : ℝ, ∀ P : W.toAffine.Point,
          ht (P + Q) ≤ 2 * ht P + C) ∧
        (∃ C : ℝ, ∀ P : W.toAffine.Point, 4 * ht P ≤ ht (2 • P) + C) ∧
        (∃ R : Finset W.toAffine.Point, ∀ P : W.toAffine.Point,
          ∃ Q ∈ R, ∃ P' : W.toAffine.Point, P = 2 • P' + Q)) :
    MordellStatement := by
  intro W hW
  obtain ⟨ht, hnonneg, hfin, htri, hdup, R, hR⟩ := H W hW
  exact Mordell_finite_generation W hW ht hnonneg hfin htri hdup R hR

/-!
## Non-vacuity check

The hypotheses of the descent theorem are satisfiable: they hold for `A = ℤ` with the
"height" `n ↦ n ^ 2`, and the descent theorem then yields that `ℤ` is finitely generated.
-/

theorem descent_of_height_int_example : AddGroup.FG ℤ := by
  classical
  refine descent_of_height (A := ℤ) (m := 2) le_rfl (fun n => ((n : ℝ)) ^ 2)
    (fun n => sq_nonneg _) ?_ ?_ ?_ ({0, 1} : Finset ℤ) ?_
  · intro B
    refine Set.Finite.subset (Set.finite_Icc (-(⌈|B|⌉ : ℤ)) (⌈|B|⌉ : ℤ)) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have hB : ((n : ℝ)) ^ 2 ≤ |B| := le_trans hn (le_abs_self B)
    have habs : |(n : ℝ)| ≤ |B| + 1 := by
      nlinarith [abs_nonneg ((n : ℝ)), sq_abs ((n : ℝ)), abs_nonneg B,
        sq_nonneg (|(n : ℝ)| - 1)]
    have hceil : (|B| : ℝ) ≤ (⌈|B|⌉ : ℤ) := Int.le_ceil _
    have h1 : |(n : ℝ)| ≤ ((⌈|B|⌉ : ℤ) : ℝ) + 1 := by linarith
    have h2 : |n| ≤ ⌈|B|⌉ + 1 := by
      have : ((|n| : ℤ) : ℝ) ≤ ((⌈|B|⌉ + 1 : ℤ) : ℝ) := by
        push_cast
        simpa [abs_le, Int.cast_abs] using h1
      exact_mod_cast this
    -- refine the bound: `n ^ 2 ≤ |B|` forces `|n| ≤ ⌈|B|⌉`
    have h3 : |n| ≤ ⌈|B|⌉ := by
      by_contra hcon
      push_neg at hcon
      have hn1 : (⌈|B|⌉ : ℤ) + 1 ≤ |n| := hcon
      have hr : ((⌈|B|⌉ : ℤ) : ℝ) + 1 ≤ |(n : ℝ)| := by
        have : (((⌈|B|⌉ + 1 : ℤ)) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn1
        push_cast at this
        simpa [Int.cast_abs] using this
      have hBnn : (0 : ℝ) ≤ |B| := abs_nonneg B
      have : |B| + 1 ≤ |(n : ℝ)| := by linarith
      nlinarith [sq_abs ((n : ℝ)), abs_nonneg ((n : ℝ))]
    have := abs_le.mp h3
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro Q
    refine ⟨2 * ((Q : ℝ)) ^ 2, ?_⟩
    intro P
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) - (Q : ℝ))]
  · refine ⟨0, fun P => ?_⟩
    have hsm : ((2 : ℕ) • P : ℤ) = 2 * P := by
      simp
    rw [hsm]
    push_cast
    nlinarith [sq_nonneg ((P : ℝ))]
  · intro P
    rcases Int.even_or_odd P with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨0, by simp, k, by rw [hk, two_nsmul]; ring⟩
    · exact ⟨1, by simp, k, by rw [hk, two_nsmul]; ring⟩

end Frontier

