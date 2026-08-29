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

/-- **Descent theorem** (the group-theoretic heart of the Mordell–Weil theorem).

Let `A` be an abelian group equipped with a real-valued "height" function `h` such that

* `hfin`  : every sublevel set `{P | h P ≤ C}` is finite;
* `htrans`: translation by a fixed element at worst doubles the height, up to a constant;
* `hdup`  : duplication at least quadruples the height, up to a constant;
* `hweak` : (weak Mordell–Weil) `A / 2A` is finite, phrased as the existence of a finite set
            of coset representatives `S` for the subgroup `2A`.

Then `A` is a finitely generated abelian group. -/
theorem fg_of_height_descent {A : Type*} [AddCommGroup A] (h : A → ℝ)
    (hfin : ∀ C : ℝ, {P : A | h P ≤ C}.Finite)
    (htrans : ∀ Q : A, ∃ C : ℝ, ∀ P : A, h (P - Q) ≤ 2 * h P + C)
    (hdup : ∃ C : ℝ, ∀ P : A, 4 * h P ≤ h (2 • P) + C)
    (hweak : ∃ S : Finset A, ∀ P : A, ∃ Q ∈ S, ∃ R : A, P = Q + 2 • R) :
    AddGroup.FG A := by
  obtain ⟨S, hS⟩ := hweak
  obtain ⟨C₂, hC₂⟩ := hdup
  choose C hC using htrans
  obtain ⟨C₁, hC₁⟩ := (S.image C).exists_le
  have hC₁' : ∀ Q ∈ S, C Q ≤ C₁ := fun Q hQ => hC₁ _ (Finset.mem_image_of_mem C hQ)
  set T : ℝ := max (C₁ + C₂) 4 with hT
  have hT4 : (4 : ℝ) ≤ T := le_max_right _ _
  have hTC : C₁ + C₂ ≤ T := le_max_left _ _
  -- The finite generating set: coset representatives together with all points of small height.
  set F : Finset A := (hfin T).toFinset with hF
  set G : Finset A := S ∪ F with hG
  have hmemF : ∀ P : A, h P ≤ T → P ∈ G := by
    intro P hP
    refine Finset.mem_union_right _ ?_
    simpa [hF, Set.Finite.mem_toFinset] using hP
  have hmemS : ∀ P ∈ S, P ∈ G := fun P hP => Finset.mem_union_left _ hP
  set K : AddSubgroup A := AddSubgroup.closure (G : Set A) with hK
  have key : ∀ n : ℕ, ∀ P : A, ⌈h P⌉₊ ≤ n → P ∈ K := by
    intro n
    induction n with
    | zero =>
        intro P hP
        have : h P ≤ 0 := by
          have := Nat.le_ceil (h P)
          rw [Nat.le_zero] at hP
          rw [hP] at this
          simpa using this
        exact AddSubgroup.subset_closure (hmemF P (this.trans (by linarith)))
    | succ n ih =>
        intro P hP
        by_cases hsmall : h P ≤ T
        · exact AddSubgroup.subset_closure (hmemF P hsmall)
        · push_neg at hsmall
          obtain ⟨Q, hQS, R, hPQR⟩ := hS P
          have hsub : P - Q = 2 • R := by rw [hPQR]; abel
          have h1 : h (2 • R) ≤ 2 * h P + C Q := by
            have := hC Q P
            rwa [hsub] at this
          have h2 : 4 * h R ≤ h (2 • R) + C₂ := hC₂ R
          have h3 : C Q ≤ C₁ := hC₁' Q hQS
          have hRle : h R ≤ h P - 1 := by linarith
          have hPn : h P ≤ (n : ℝ) + 1 := by
            have h4 : h P ≤ (⌈h P⌉₊ : ℝ) := Nat.le_ceil (h P)
            have h5 : ((⌈h P⌉₊ : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hP
            push_cast at h5
            linarith
          have hRceil : ⌈h R⌉₊ ≤ n := by
            rw [Nat.ceil_le]
            linarith
          have hRK : R ∈ K := ih R hRceil
          have : (2 : ℕ) • R ∈ K := AddSubgroup.nsmul_mem K hRK 2
          rw [hPQR]
          exact AddSubgroup.add_mem K (AddSubgroup.subset_closure (hmemS Q hQS)) this
  rw [AddGroup.fg_iff]
  refine ⟨(G : Set A), ?_, G.finite_toSet⟩
  rw [eq_top_iff]
  intro P _
  exact key ⌈h P⌉₊ P le_rfl

/-- **Mordell's theorem** (finite generation of the Mordell–Weil group), reduced to its two
standard inputs.

For an elliptic curve `E` over `ℚ`, the group `E(ℚ)` of rational points is finitely generated,
given a height function `h` on `E(ℚ)` satisfying the classical estimates

* finiteness of sets of bounded height,
* `h (P - Q) ≤ 2 * h P + C Q` for translation by a fixed point,
* `4 * h P ≤ h (2 • P) + C` for duplication,

together with the weak Mordell–Weil theorem, stated as the existence of a finite set of
representatives for the cosets of `2 · E(ℚ)` in `E(ℚ)`.

This is the classical descent argument: the theorem is a Lean-checked reduction of Mordell's
theorem to the theory of heights and to weak Mordell–Weil. -/
theorem Mordell_finite_generation {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h : E.toAffine.Point → ℝ)
    (hfin : ∀ C : ℝ, {P : E.toAffine.Point | h P ≤ C}.Finite)
    (htrans : ∀ Q : E.toAffine.Point, ∃ C : ℝ,
      ∀ P : E.toAffine.Point, h (P - Q) ≤ 2 * h P + C)
    (hdup : ∃ C : ℝ, ∀ P : E.toAffine.Point, 4 * h P ≤ h (2 • P) + C)
    (hweak : ∃ S : Finset E.toAffine.Point, ∀ P : E.toAffine.Point,
      ∃ Q ∈ S, ∃ R : E.toAffine.Point, P = Q + 2 • R) :
    AddGroup.FG E.toAffine.Point :=
  fg_of_height_descent h hfin htrans hdup hweak

end Frontier

