/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Belyi's theorem is formalized in its genus-zero (polynomial) form, which is the arithmetic heart
of the theorem: the "curve" is the projective line together with a finite set `S` of marked
complex points, and a Belyi map is given by a polynomial `f ∈ ℚ[X]` — viewed as a map
`ℙ¹ → ℙ¹` defined over `ℚ` for which `∞` is totally ramified over `∞`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` (i.e. all elements of
`S` are algebraic over `ℚ`) if and only if there is a nonconstant such `f` which maps `S` into
`{0, 1}` and all of whose critical values lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`.

The easy direction is elementary. The hard direction is Belyi's algorithm, carried out here in
two stages:

* `Math2.stageA`: composing with minimal polynomials, one finds a nonconstant `f ∈ ℚ[X]` for
  which the images of the marked points and all critical values are rational. Termination is
  measured by `Math2.muA`, a sum of factorials of the degrees of the algebraic numbers involved.
* `Math2.stageB`: a finite set of rationals is collapsed into `{0, 1}` by repeatedly composing
  with the polynomials `c · x^m (1-x)^n` (after an affine change of coordinates), each step
  strictly decreasing the number of relevant rational values.
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

set_option grind.warning false

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Critical points and critical values -/

/-- The critical points in `ℂ` of a polynomial with rational coefficients. -/

theorem stageB : ∀ (N : ℕ) (T : Finset ℚ), (insert (0 : ℚ) (insert 1 T)).card ≤ N →
    ∃ g : ℚ[X], 1 ≤ g.natDegree ∧ (∀ t ∈ T, g.eval t = 0 ∨ g.eval t = 1) ∧
      (∀ w : ℂ, aeval w (derivative g) = 0 → aeval w g = 0 ∨ aeval w g = 1) := by
  intro N
  induction N with
  | zero =>
    intro T hT
    simp [Finset.card_eq_zero] at hT
  | succ N ih =>
    intro T hT
    by_cases hsimple : ∀ t ∈ T, t = 0 ∨ t = 1
    · refine ⟨X, by simp, ?_, ?_⟩
      · intro t ht
        rcases hsimple t ht with h | h <;> simp [h]
      · intro w hw
        simp at hw
    · push_neg at hsimple
      obtain ⟨b, hbT, hb0, hb1⟩ := hsimple
      set U : Finset ℚ := insert 0 (insert 1 T) with hU
      have h0U : (0 : ℚ) ∈ U := by simp [hU]
      have h1U : (1 : ℚ) ∈ U := by simp [hU]
      have hbU : b ∈ U := by simp [hU, hbT]
      have hne : U.Nonempty := ⟨0, h0U⟩
      have hcard3 : 3 ≤ U.card := by
        have hsub : ({0, 1, b} : Finset ℚ) ⊆ U := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have hc3 : ({0, 1, b} : Finset ℚ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [Ne.symm hb0]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hb1]), Finset.card_singleton]
        calc 3 = ({0, 1, b} : Finset ℚ).card := hc3.symm
          _ ≤ U.card := Finset.card_le_card hsub
      -- pick the smallest, some middle, and the largest element of `U`
      obtain ⟨a, m, c, haU, hmU, hcU, ham, hmc⟩ :
          ∃ a m c : ℚ, a ∈ U ∧ m ∈ U ∧ c ∈ U ∧ a < m ∧ m < c := by
        have haU : U.min' hne ∈ U := U.min'_mem hne
        have hcU : U.max' hne ∈ U := U.max'_mem hne
        have hsub : ({U.min' hne, U.max' hne} : Finset ℚ) ⊆ U := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hkey := Finset.card_sdiff_add_card_eq_card hsub
        have h2 : ({U.min' hne, U.max' hne} : Finset ℚ).card ≤ 2 :=
          (Finset.card_insert_le _ _).trans (by simp)
        have hV : (U \ {U.min' hne, U.max' hne}).Nonempty := by
          rw [← Finset.card_pos]; omega
        obtain ⟨m, hm⟩ := hV
        rw [Finset.mem_sdiff] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
        exact ⟨U.min' hne, m, U.max' hne, haU, hm.1, hcU,
          lt_of_le_of_ne (U.min'_le m hm.1) (Ne.symm hm.2.1),
          lt_of_le_of_ne (U.le_max' m hm.1) hm.2.2⟩
      obtain ⟨P, hP1, hPa, hPc, hPm, hPcrit⟩ := exists_belyi_three ham hmc
      set T' : Finset ℚ := U.image (fun t => P.eval t) with hT'
      have h0T' : (0 : ℚ) ∈ T' := by
        rw [hT', Finset.mem_image]; exact ⟨a, haU, hPa⟩
      have h1T' : (1 : ℚ) ∈ T' := by
        rw [hT', Finset.mem_image]; exact ⟨m, hmU, hPm⟩
      have hins : insert (0 : ℚ) (insert 1 T') = T' := by
        rw [Finset.insert_eq_self.2 h1T', Finset.insert_eq_self.2 h0T']
      have hcardT' : T'.card ≤ U.card - 1 := by
        have hsub3 : ({a, m, c} : Finset ℚ) ⊆ U := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have hc3 : ({a, m, c} : Finset ℚ).card = 3 := by
          have hane : a ∉ ({m, c} : Finset ℚ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨ne_of_lt ham, ne_of_lt (ham.trans hmc)⟩
          have hmne : m ∉ ({c} : Finset ℚ) := by
            simp only [Finset.mem_singleton]
            exact ne_of_lt hmc
          rw [Finset.card_insert_of_notMem hane, Finset.card_insert_of_notMem hmne,
            Finset.card_singleton]
        have hkey := Finset.card_sdiff_add_card_eq_card hsub3
        have hUeq : (U \ {a, m, c}) ∪ {a, m, c} = U := Finset.sdiff_union_of_subset hsub3
        have himg : T' = (U \ {a, m, c}).image (fun t => P.eval t)
            ∪ ({a, m, c} : Finset ℚ).image (fun t => P.eval t) := by
          rw [hT', ← Finset.image_union, hUeq]
        have hsmall : ({a, m, c} : Finset ℚ).image (fun t => P.eval t) ⊆ ({0, 1} : Finset ℚ) := by
          intro y hy
          simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          obtain ⟨x, hx, rfl⟩ := hy
          rcases hx with rfl | rfl | rfl
          · left; exact hPa
          · right; exact hPm
          · left; exact hPc
        have hb1' : (({a, m, c} : Finset ℚ).image (fun t => P.eval t)).card ≤ 2 :=
          (Finset.card_le_card hsmall).trans (by simp)
        have hb2' : ((U \ {a, m, c}).image (fun t => P.eval t)).card ≤ (U \ {a, m, c}).card :=
          Finset.card_image_le
        have := Finset.card_union_le ((U \ {a, m, c}).image (fun t => P.eval t))
          (({a, m, c} : Finset ℚ).image (fun t => P.eval t))
        rw [himg]
        omega
      obtain ⟨g, hg1, hgT', hgc⟩ := ih T' (by rw [hins]; omega)
      have hg0 : g.eval 0 = 0 ∨ g.eval 0 = 1 := hgT' 0 h0T'
      have hg1' : g.eval 1 = 0 ∨ g.eval 1 = 1 := hgT' 1 h1T'
      refine ⟨g.comp P, ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_comp]
        calc 1 = 1 * 1 := by norm_num
          _ ≤ g.natDegree * P.natDegree := Nat.mul_le_mul hg1 hP1
      · intro t ht
        have htU : t ∈ U := by simp [hU, ht]
        have : P.eval t ∈ T' := by rw [hT', Finset.mem_image]; exact ⟨t, htU, rfl⟩
        rw [eval_comp]
        exact hgT' _ this
      · intro w hw
        rw [Polynomial.derivative_comp, map_mul, mul_eq_zero] at hw
        have hcast0 : aeval (0 : ℂ) g = ((g.eval 0 : ℚ) : ℂ) := by simpa using aeval_ratCast 0 g
        have hcast1 : aeval (1 : ℂ) g = ((g.eval 1 : ℚ) : ℂ) := by simpa using aeval_ratCast 1 g
        rcases hw with hw | hw
        · rw [Polynomial.aeval_comp]
          rcases hPcrit w hw with h | h
          · rw [h, hcast0]
            rcases hg0 with h' | h' <;> rw [h'] <;> norm_num
          · rw [h, hcast1]
            rcases hg1' with h' | h' <;> rw [h'] <;> norm_num
        · rw [Polynomial.aeval_comp] at hw
          rw [Polynomial.aeval_comp]
          exact hgc _ hw

/-! ## Stage A: making all the relevant values rational -/

/-- The measure controlling the induction in Stage A. -/
