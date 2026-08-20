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
def critPts (p : ℚ[X]) : Finset ℂ :=
  ((derivative p).map (algebraMap ℚ ℂ)).roots.toFinset

/-- The critical values in `ℂ` of a polynomial with rational coefficients. -/
def critVals (p : ℚ[X]) : Finset ℂ := (critPts p).image (fun w => aeval w p)

lemma derivative_ne_zero_of_one_le_natDegree {p : ℚ[X]} (hp : 1 ≤ p.natDegree) :
    derivative p ≠ 0 := by
  intro h0
  have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h0
  omega

lemma mem_critPts {p : ℚ[X]} (hp : 1 ≤ p.natDegree) {w : ℂ}
    (hw : aeval w (derivative p) = 0) : w ∈ critPts p := by
  have hne : ((derivative p).map (algebraMap ℚ ℂ)) ≠ 0 := by
    simpa using (Polynomial.map_ne_zero_iff (f := algebraMap ℚ ℂ)
      (RingHom.injective _)).2 (derivative_ne_zero_of_one_le_natDegree hp)
  simp only [critPts, Multiset.mem_toFinset, Polynomial.mem_roots hne, IsRoot.def]
  rw [Polynomial.eval_map, ← Polynomial.aeval_def]
  exact hw

lemma aeval_eq_zero_of_mem_critPts {p : ℚ[X]} {w : ℂ} (hw : w ∈ critPts p) :
    aeval w (derivative p) = 0 := by
  simp only [critPts, Multiset.mem_toFinset] at hw
  have h := Polynomial.isRoot_of_mem_roots hw
  rw [IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at h
  exact h

lemma card_critPts_le (p : ℚ[X]) : (critPts p).card ≤ p.natDegree - 1 := by
  refine le_trans (Multiset.toFinset_card_le _) ?_
  refine le_trans (Polynomial.card_roots' _) ?_
  rw [Polynomial.natDegree_map]
  exact Polynomial.natDegree_derivative_le p

lemma isAlgebraic_of_mem_critPts {p : ℚ[X]} (hp : 1 ≤ p.natDegree) {w : ℂ}
    (hw : w ∈ critPts p) : IsAlgebraic ℚ w :=
  ⟨derivative p, derivative_ne_zero_of_one_le_natDegree hp, aeval_eq_zero_of_mem_critPts hw⟩

/-! ## Degrees of algebraic numbers -/

/-- The degree of an algebraic number over `ℚ`. -/
def degQ (z : ℂ) : ℕ := (minpoly ℚ z).natDegree

lemma isIntegral_aeval {z : ℂ} (hz : IsAlgebraic ℚ z) (p : ℚ[X]) :
    IsIntegral ℚ (aeval z p) := by
  haveI : FiniteDimensional ℚ ℚ⟮z⟯ := adjoin.finiteDimensional hz.isIntegral
  have hmem : (aeval z p) ∈ ℚ⟮z⟯ :=
    (IntermediateField.algebra_adjoin_le_adjoin ℚ {z})
      (Polynomial.aeval_mem_adjoin_singleton ℚ (p := p) z)
  have h1 : IsIntegral ℚ (⟨aeval z p, hmem⟩ : ℚ⟮z⟯) := Algebra.IsIntegral.isIntegral _
  exact h1.map (ℚ⟮z⟯.val)

lemma isAlgebraic_aeval {z : ℂ} (hz : IsAlgebraic ℚ z) (p : ℚ[X]) :
    IsAlgebraic ℚ (aeval z p) := (isIntegral_aeval hz p).isAlgebraic

/-- Evaluating a rational polynomial does not increase the degree of an algebraic number. -/
lemma degQ_aeval_le {z : ℂ} (hz : IsAlgebraic ℚ z) (p : ℚ[X]) :
    degQ (aeval z p) ≤ degQ z := by
  have hi : IsIntegral ℚ z := hz.isIntegral
  haveI hfin : FiniteDimensional ℚ ℚ⟮z⟯ := adjoin.finiteDimensional hi
  have hmem : (aeval z p) ∈ ℚ⟮z⟯ :=
    (IntermediateField.algebra_adjoin_le_adjoin ℚ {z})
      (Polynomial.aeval_mem_adjoin_singleton ℚ (p := p) z)
  have hle : ℚ⟮aeval z p⟯ ≤ ℚ⟮z⟯ := (IntermediateField.adjoin_simple_le_iff).2 hmem
  haveI : Module.Finite ℚ (Subalgebra.toSubmodule ℚ⟮z⟯.toSubalgebra) := hfin
  have key := Submodule.finrank_mono (R := ℚ) (M := ℂ)
    (s := (ℚ⟮aeval z p⟯ : IntermediateField ℚ ℂ).toSubmodule)
    (t := (ℚ⟮z⟯ : IntermediateField ℚ ℂ).toSubmodule) (by exact_mod_cast hle)
  simp only [degQ]
  rw [← IntermediateField.adjoin.finrank hi,
    ← IntermediateField.adjoin.finrank (isIntegral_aeval hz p)]
  exact key

lemma degQ_le_of_aeval_eq_zero {z : ℂ} {p : ℚ[X]} (hp : p ≠ 0) (hz : aeval z p = 0) :
    degQ z ≤ p.natDegree :=
  Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero ℚ z hp hz)

lemma degQ_zero : degQ 0 = 1 := by simp [degQ]

lemma one_le_degQ {z : ℂ} (hz : IsAlgebraic ℚ z) : 1 ≤ degQ z :=
  minpoly.natDegree_pos hz.isIntegral

/-- A rational number attached to `z`; it equals `z` when `z` has degree one. -/
def ratOf (z : ℂ) : ℚ := -(minpoly ℚ z).coeff 0

lemma eq_ratOf_of_degQ_le_one {z : ℂ} (hz : IsAlgebraic ℚ z) (h : degQ z ≤ 1) :
    z = (ratOf z : ℂ) := by
  have hm : (minpoly ℚ z).Monic := minpoly.monic hz.isIntegral
  have hdeg : (minpoly ℚ z).natDegree = 1 := le_antisymm h (minpoly.natDegree_pos hz.isIntegral)
  have hXC := Polynomial.eq_X_add_C_of_natDegree_le_one (p := minpoly ℚ z) (by omega)
  have hc1 : (minpoly ℚ z).coeff 1 = 1 := by
    have hl := hm.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at hl
  rw [hc1] at hXC
  have h0 : (Polynomial.aeval z) (minpoly ℚ z) = 0 := minpoly.aeval ℚ z
  rw [hXC] at h0
  simp only [ratOf] at h0 ⊢
  simp only [map_add, map_one, one_mul, aeval_X, aeval_C, eq_ratCast] at h0
  push_cast
  linear_combination h0

/-! ## The elementary Belyi polynomials -/

lemma aeval_ratCast (t : ℚ) (g : ℚ[X]) : aeval ((t : ℂ)) g = ((g.eval t : ℚ) : ℂ) := by
  simpa using Polynomial.aeval_algebraMap_apply (A := ℚ) (B := ℂ) (R := ℚ) t g

lemma one_le_natDegree_of_eval_ne {p : ℚ[X]} {x y : ℚ} (h : p.eval x ≠ p.eval y) :
    1 ≤ p.natDegree := by
  by_contra hc
  push_neg at hc
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 (show p.natDegree = 0 by omega)
  rw [← ha] at h
  simp at h

lemma exists_num_den {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ lam = (m : ℚ) / ((m : ℚ) + n) := by
  have hnum : 0 < lam.num := Rat.num_pos.2 h0
  have hlt : lam.num < lam.den := Rat.lt_one_iff_num_lt_denom.mp h1
  refine ⟨lam.num.toNat, lam.den - lam.num.toNat, by omega, by omega, ?_⟩
  have hd : ((lam.num.toNat : ℚ) + ((lam.den - lam.num.toNat : ℕ) : ℚ)) = (lam.den : ℚ) := by
    have hle : (lam.num.toNat : ℕ) ≤ lam.den := by omega
    push_cast [Nat.cast_sub hle]
    ring
  rw [hd]
  have hcast : ((lam.num.toNat : ℕ) : ℚ) = (lam.num : ℚ) :=
    mod_cast Int.toNat_of_nonneg (le_of_lt hnum)
  rw [hcast, Rat.num_div_den]

/-- For `0 < lam < 1` rational there is a polynomial with rational coefficients which kills
`0` and `1`, sends `lam` to `1`, and all of whose critical values lie in `{0, 1}`. -/
lemma exists_belyi_base {lam : ℚ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ B : ℚ[X], 1 ≤ B.natDegree ∧ B.eval 0 = 0 ∧ B.eval 1 = 0 ∧ B.eval lam = 1 ∧
      (∀ w : ℂ, aeval w (derivative B) = 0 → aeval w B = 0 ∨ aeval w B = 1) := by
  obtain ⟨m, n, hm, hn, hlam0⟩ := exists_num_den h0 h1
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hlam : lam = ((M : ℚ) + 1) / ((M : ℚ) + (N : ℚ) + 2) := by
    rw [hlam0]; push_cast; ring_nf
  clear hlam0
  set D : ℚ := (M : ℚ) + (N : ℚ) + 2 with hD
  have hDpos : 0 < D := by positivity
  set c : ℚ := D ^ (M + N + 2) / (((M : ℚ) + 1) ^ (M + 1) * ((N : ℚ) + 1) ^ (N + 1)) with hc
  set B : ℚ[X] := C c * X ^ (M + 1) * (1 - X) ^ (N + 1) with hB
  have hcne : c ≠ 0 := by rw [hc]; positivity
  have hB0 : B.eval 0 = 0 := by simp [hB]
  have hB1 : B.eval 1 = 0 := by simp [hB]
  have h1l : 1 - lam = ((N : ℚ) + 1) / D := by rw [hlam]; field_simp; rw [hD]; ring
  have expand : B.eval lam = c * lam ^ (M + 1) * (1 - lam) ^ (N + 1) := by simp [hB]
  have hBlam : B.eval lam = 1 := by
    rw [expand, h1l, hlam, div_pow, div_pow, hc]
    have hpow : D ^ (M + 1) * D ^ (N + 1) = D ^ (M + N + 2) := by rw [← pow_add]; ring_nf
    field_simp
    ring
  refine ⟨B, one_le_natDegree_of_eval_ne (x := 0) (y := lam) (by rw [hB0, hBlam]; norm_num),
    hB0, hB1, hBlam, ?_⟩
  have hderiv : derivative B = C c * X ^ M * (1 - X) ^ N * (C ((M : ℚ) + 1) - C D * X) := by
    rw [hB, hD]
    simp only [derivative_mul, derivative_pow, derivative_X, derivative_C, derivative_one,
      derivative_sub, zero_mul, zero_add, mul_one, Nat.add_sub_cancel]
    push_cast
    simp only [C_add, C_1, map_ofNat]
    ring
  intro w hw
  rw [hderiv, hD] at hw
  simp only [map_mul, map_sub, map_pow, map_one, aeval_C, aeval_X, eq_ratCast,
    mul_eq_zero, sub_eq_zero, pow_eq_zero_iff'] at hw
  push_cast at hw
  have hcast0 : aeval (0 : ℂ) B = ((B.eval 0 : ℚ) : ℂ) := by simpa using aeval_ratCast 0 B
  have hcast1 : aeval (1 : ℂ) B = ((B.eval 1 : ℚ) : ℂ) := by simpa using aeval_ratCast 1 B
  have hcastl : aeval ((lam : ℚ) : ℂ) B = ((B.eval lam : ℚ) : ℂ) := aeval_ratCast lam B
  have hDne : ((M : ℂ) + (N : ℂ) + 2) ≠ 0 := by
    have h2 : (((D : ℚ)) : ℂ) ≠ 0 := mod_cast (ne_of_gt hDpos)
    rw [hD] at h2
    push_cast at h2
    exact h2
  rcases hw with (h | h) | h
  · rcases h with h | h
    · exact absurd (mod_cast h : (c : ℚ) = 0) hcne
    · left
      rw [h.1, hcast0, hB0]; norm_num
  · left
    rw [← h.1, hcast1, hB1]; norm_num
  · right
    have hwlam : w = ((lam : ℚ) : ℂ) := by
      rw [hlam, hD]
      push_cast
      field_simp
      linear_combination -h
    rw [hwlam, hcastl, hBlam]; norm_num

/-- Given three rationals `a < b < c` there is a polynomial with rational coefficients sending
`a, c` to `0`, `b` to `1`, and all of whose critical values lie in `{0, 1}`. -/
lemma exists_belyi_three {a b c : ℚ} (hab : a < b) (hbc : b < c) :
    ∃ P : ℚ[X], 1 ≤ P.natDegree ∧ P.eval a = 0 ∧ P.eval c = 0 ∧ P.eval b = 1 ∧
      (∀ w : ℂ, aeval w (derivative P) = 0 → aeval w P = 0 ∨ aeval w P = 1) := by
  have hca : (0 : ℚ) < c - a := by linarith
  set lam : ℚ := (b - a) / (c - a) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; apply div_pos <;> linarith
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hca]; linarith
  obtain ⟨B, _, hB0, hBone, hBlam, hBc⟩ := exists_belyi_base hlam0 hlam1
  set A : ℚ[X] := C (c - a)⁻¹ * (X - C a) with hA
  have hAa : A.eval a = 0 := by simp [hA]
  have hAc : A.eval c = 1 := by
    simp only [hA, eval_mul, eval_C, eval_sub, eval_X]
    field_simp
  have hAb : A.eval b = lam := by
    simp only [hA, eval_mul, eval_C, eval_sub, eval_X, hlam]
    field_simp
  refine ⟨B.comp A, ?_, ?_, ?_, ?_, ?_⟩
  · refine one_le_natDegree_of_eval_ne (x := a) (y := b) ?_
    rw [eval_comp, eval_comp, hAa, hAb, hB0, hBlam]
    norm_num
  · rw [eval_comp, hAa, hB0]
  · rw [eval_comp, hAc, hBone]
  · rw [eval_comp, hAb, hBlam]
  · intro w hw
    rw [derivative_comp, map_mul, mul_eq_zero] at hw
    have hdA : derivative A = C (c - a)⁻¹ := by simp [hA]
    rcases hw with hw | hw
    · rw [hdA] at hw
      simp only [aeval_C, eq_ratCast, Rat.cast_eq_zero, inv_eq_zero, sub_eq_zero] at hw
      exact absurd hw (by intro h; rw [h] at hca; simp at hca)
    · rw [aeval_comp] at hw
      rw [aeval_comp]
      exact hBc _ hw

/-! ## Stage B: collapsing a finite set of rational values to `{0,1}` -/

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
def muA (S : Finset ℂ) : ℕ := ∑ z ∈ S, (degQ z + 1)!

lemma factorial_ineq {d : ℕ} (hd : 2 ≤ d) : 2 + (d - 1) * d ! < (d + 1)! := by
  have hfac2 : 2 ≤ d ! := by
    calc 2 = 2 ! := rfl
      _ ≤ d ! := Nat.factorial_le hd
  have hexp : (d + 1)! = (d - 1) * d ! + 2 * d ! := by
    rw [Nat.factorial_succ, ← add_mul]
    congr 1
    omega
  omega

/-- One step of the Stage A induction strictly decreases the measure `muA`. -/
lemma muA_step {s0 : ℂ} {S : Finset ℂ} (hS : ∀ z ∈ S, IsAlgebraic ℚ z) (hs0S : s0 ∈ S)
    (hd : 2 ≤ degQ s0) :
    muA (S.image (fun z => aeval z (minpoly ℚ s0)) ∪ critVals (minpoly ℚ s0)) < muA S := by
  set mp : ℚ[X] := minpoly ℚ s0 with hmp
  set d : ℕ := mp.natDegree with hdd
  have hdegs0 : degQ s0 = d := rfl
  have hd2 : 2 ≤ d := by rw [← hdegs0]; exact hd
  have hmp1 : 1 ≤ mp.natDegree := by omega
  have h1 : muA (S.image (fun z => aeval z mp) ∪ critVals mp)
      ≤ muA (S.image (fun z => aeval z mp)) + muA (critVals mp) := by
    simp only [muA]
    have h := Finset.sum_union_inter (s₁ := S.image (fun z => aeval z mp)) (s₂ := critVals mp)
      (f := fun z => (degQ z + 1)!)
    omega
  have h2 : muA (S.image (fun z => aeval z mp)) ≤ ∑ z ∈ S, (degQ (aeval z mp) + 1)! :=
    Finset.sum_image_le_of_nonneg (fun u _ => Nat.zero_le _)
  have h3 : ∑ z ∈ S, (degQ (aeval z mp) + 1)!
      = (degQ (aeval s0 mp) + 1)! + ∑ z ∈ S.erase s0, (degQ (aeval z mp) + 1)! :=
    (Finset.add_sum_erase S _ hs0S).symm
  have h4 : (degQ (aeval s0 mp) + 1)! = 2 := by
    rw [show aeval s0 mp = 0 from minpoly.aeval ℚ s0, degQ_zero]
    rfl
  have h5 : ∑ z ∈ S.erase s0, (degQ (aeval z mp) + 1)! ≤ ∑ z ∈ S.erase s0, (degQ z + 1)! :=
    Finset.sum_le_sum (fun z hz => Nat.factorial_le (by
      have := degQ_aeval_le (hS z (Finset.mem_of_mem_erase hz)) mp; omega))
  have hcritbd : ∀ y ∈ critVals mp, (degQ y + 1)! ≤ d ! := by
    intro y hy
    simp only [critVals, Finset.mem_image] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwalg : IsAlgebraic ℚ w := isAlgebraic_of_mem_critPts hmp1 hw
    have hwd : degQ w ≤ d - 1 := by
      have hle := degQ_le_of_aeval_eq_zero (derivative_ne_zero_of_one_le_natDegree hmp1)
        (aeval_eq_zero_of_mem_critPts hw)
      have := Polynomial.natDegree_derivative_le mp
      omega
    have hle2 := degQ_aeval_le hwalg mp
    exact Nat.factorial_le (by omega)
  have h6 : muA (critVals mp) ≤ (critVals mp).card * d ! := by
    simpa [muA, smul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hcritbd
  have h7 : (critVals mp).card ≤ d - 1 :=
    le_trans Finset.card_image_le (card_critPts_le mp)
  have h8 : muA S = (d + 1)! + ∑ z ∈ S.erase s0, (degQ z + 1)! := by
    simp only [muA]
    rw [← Finset.add_sum_erase S _ hs0S, hdegs0]
  have h9 : (critVals mp).card * d ! ≤ (d - 1) * d ! := Nat.mul_le_mul_right _ h7
  have key := factorial_ineq hd2
  omega

theorem stageA : ∀ (N : ℕ) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) → muA S ≤ N →
    ∃ (f : ℚ[X]) (T : Finset ℚ), 1 ≤ f.natDegree ∧
      (∀ z ∈ S, ∃ t ∈ T, aeval z f = (t : ℂ)) ∧
      (∀ w : ℂ, aeval w (derivative f) = 0 → ∃ t ∈ T, aeval w f = (t : ℂ)) := by
  intro N
  induction N with
  | zero =>
    intro S _ hmu
    have hSempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have hle : (degQ z + 1)! ≤ muA S :=
        Finset.single_le_sum (f := fun z => (degQ z + 1)!) (fun i _ => Nat.zero_le _) hz
      have := Nat.factorial_pos (degQ z + 1)
      omega
    refine ⟨X, ∅, by simp, ?_, ?_⟩
    · intro z hz; rw [hSempty] at hz; simp at hz
    · intro w hw; simp at hw
  | succ N ih =>
    intro S hS hmu
    by_cases hall : ∀ z ∈ S, degQ z ≤ 1
    · refine ⟨X, S.image ratOf, by simp, ?_, ?_⟩
      · intro z hz
        exact ⟨ratOf z, Finset.mem_image_of_mem _ hz, by
          simpa using eq_ratOf_of_degQ_le_one (hS z hz) (hall z hz)⟩
      · intro w hw; simp at hw
    · push_neg at hall
      obtain ⟨s0, hs0S, hs0d⟩ := hall
      have hd2 : 2 ≤ degQ s0 := hs0d
      set mp : ℚ[X] := minpoly ℚ s0 with hmp
      have hmp1 : 1 ≤ mp.natDegree := by
        have hdegs0 : degQ s0 = mp.natDegree := rfl
        omega
      set S' : Finset ℂ := S.image (fun z => aeval z mp) ∪ critVals mp with hS'def
      have halg' : ∀ y ∈ S', IsAlgebraic ℚ y := by
        intro y hy
        rw [hS'def, Finset.mem_union] at hy
        rcases hy with hy | hy
        · rw [Finset.mem_image] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          exact isAlgebraic_aeval (hS z hz) mp
        · rw [critVals, Finset.mem_image] at hy
          obtain ⟨w, hw, rfl⟩ := hy
          exact isAlgebraic_aeval (isAlgebraic_of_mem_critPts hmp1 hw) mp
      have hmu' : muA S' ≤ N := by
        have hstep : muA S' < muA S := muA_step hS hs0S hd2
        omega
      obtain ⟨f', T', hf'1, hf'S, hf'C⟩ := ih S' halg' hmu'
      refine ⟨f'.comp mp, T', ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_comp]
        calc 1 = 1 * 1 := by norm_num
          _ ≤ f'.natDegree * mp.natDegree := Nat.mul_le_mul hf'1 hmp1
      · intro z hz
        have hmem : aeval z mp ∈ S' := by
          rw [hS'def, Finset.mem_union]; exact Or.inl (Finset.mem_image_of_mem _ hz)
        obtain ⟨t, htT, ht⟩ := hf'S _ hmem
        exact ⟨t, htT, by rw [Polynomial.aeval_comp]; exact ht⟩
      · intro w hw
        rw [Polynomial.derivative_comp, map_mul, mul_eq_zero] at hw
        rcases hw with hw | hw
        · have hwc : w ∈ critPts mp := mem_critPts hmp1 hw
          have hmem : aeval w mp ∈ S' := by
            rw [hS'def, Finset.mem_union]
            exact Or.inr (Finset.mem_image_of_mem _ hwc)
          obtain ⟨t, htT, ht⟩ := hf'S _ hmem
          exact ⟨t, htT, by rw [Polynomial.aeval_comp]; exact ht⟩
        · rw [Polynomial.aeval_comp] at hw
          obtain ⟨t, htT, ht⟩ := hf'C _ hw
          exact ⟨t, htT, by rw [Polynomial.aeval_comp]; exact ht⟩

/-! ## Belyi's theorem in genus zero -/

/-- **Belyi's theorem** (polynomial / genus zero form).

A finite set `S` of complex numbers consists of algebraic numbers (i.e. the marked points are
defined over `ℚ̄`) if and only if there is a nonconstant map `f : ℙ¹ → ℙ¹` defined over `ℚ`
(here given by a polynomial, so that `∞` is totally ramified over `∞`) which sends `S` into
`{0, 1}` and whose critical values all lie in `{0, 1}`, i.e. which is unramified outside
`{0, 1, ∞}`. -/
theorem belyi_theorem (S : Finset ℂ) :
    (∀ z ∈ S, IsAlgebraic ℚ z) ↔
      ∃ f : ℚ[X], 1 ≤ f.natDegree ∧
        (∀ z ∈ S, aeval z f = 0 ∨ aeval z f = 1) ∧
        (∀ w : ℂ, aeval w (derivative f) = 0 → aeval w f = 0 ∨ aeval w f = 1) := by
  constructor
  · intro hS
    obtain ⟨f, T, hf1, hfS, hfC⟩ := stageA (muA S) S hS le_rfl
    obtain ⟨g, hg1, hgT, hgC⟩ := stageB (insert (0 : ℚ) (insert 1 T)).card T le_rfl
    refine ⟨g.comp f, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_comp]
      calc 1 = 1 * 1 := by norm_num
        _ ≤ g.natDegree * f.natDegree := Nat.mul_le_mul hg1 hf1
    · intro z hz
      obtain ⟨t, htT, ht⟩ := hfS z hz
      rw [Polynomial.aeval_comp, ht, aeval_ratCast]
      rcases hgT t htT with h | h <;> simp [h]
    · intro w hw
      rw [Polynomial.derivative_comp, map_mul, mul_eq_zero] at hw
      rcases hw with hw | hw
      · obtain ⟨t, htT, ht⟩ := hfC w hw
        rw [Polynomial.aeval_comp, ht, aeval_ratCast]
        rcases hgT t htT with h | h <;> simp [h]
      · rw [Polynomial.aeval_comp] at hw
        rw [Polynomial.aeval_comp]
        exact hgC _ hw
  · rintro ⟨f, hf1, hfS, -⟩ z hz
    have hf0 : f ≠ 0 := fun h => by simp [h] at hf1
    rcases hfS z hz with h | h
    · exact ⟨f, hf0, h⟩
    · refine ⟨f - 1, ?_, ?_⟩
      · intro h1
        have : f = 1 := by linear_combination (norm := ring_nf) h1
        rw [this] at hf1
        simp at hf1
      · simp [h]

end

end Math2

