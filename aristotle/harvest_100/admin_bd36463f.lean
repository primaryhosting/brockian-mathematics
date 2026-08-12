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

/-
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`.
(For a set with infinitely many points below `Λ` this is `0`, by the convention for
`Set.ncard`; the `Discrete` hypothesis below rules out that degenerate case.) -/
noncomputable def counting (S : Set ℝ) (L : ℝ) : ℕ := (S ∩ Set.Iic L).ncard

/-- A spectrum `S ⊆ ℝ` is *discrete* when only finitely many of its points lie below
any given threshold. -/
def Discrete (S : Set ℝ) : Prop := ∀ L : ℝ, (S ∩ Set.Iic L).Finite

/-- The spectrum `S` *matches the Weyl law* with constant `C > 0` and exponent `p > 0`
when its counting function is asymptotic to `C · Λ ^ p` as `Λ → ∞`. -/
def WeylLawMatch (S : Set ℝ) (C p : ℝ) : Prop :=
  0 < C ∧ 0 < p ∧
    Tendsto (fun L : ℝ => (counting S L : ℝ) / (C * L ^ p)) atTop (𝓝 1)

/-- The Weyl main term `Λ ↦ C · Λ ^ p` diverges when `C > 0` and `p > 0`. -/
lemma tendsto_weyl_main_term {C p : ℝ} (hC : 0 < C) (hp : 0 < p) :
    Tendsto (fun L : ℝ => C * L ^ p) atTop atTop :=
  Tendsto.const_mul_atTop hC (tendsto_rpow_atTop hp)

/-- Eventually in `Λ`, the counting function equals the Weyl main term multiplied by
the (asymptotically unit) ratio. -/
lemma eventuallyEq_counting_mul_ratio (S : Set ℝ) {C p : ℝ} (hC : 0 < C) :
    (fun L : ℝ => (C * L ^ p) * ((counting S L : ℝ) / (C * L ^ p)))
      =ᶠ[atTop] fun L : ℝ => (counting S L : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hpow : (0 : ℝ) < L ^ p := Real.rpow_pos_of_pos hL p
  have hne : (C * L ^ p) ≠ 0 := by positivity
  field_simp

/-- **The counting function diverges.**

If a spectrum `S ⊆ ℝ` is discrete and matches a Weyl law `N(Λ) ∼ C · Λ ^ p` with
`C > 0` and `p > 0`, then its eigenvalue counting function diverges:
`N(Λ) → ∞` as `Λ → ∞`.

The result is unconditional: nothing beyond discreteness and the Weyl-law match is
assumed. The discreteness hypothesis is retained because it is part of the intended
spectral setting, but the divergence already follows from the Weyl-law match alone. -/
theorem counting_diverges_of_discrete_and_WeylLawMatch
    (S : Set ℝ) (C p : ℝ) (_hdisc : Discrete S) (hW : WeylLawMatch S C p) :
    Tendsto (fun L : ℝ => (counting S L : ℝ)) atTop atTop := by
  obtain ⟨hC, hp, hratio⟩ := hW
  have hmain : Tendsto (fun L : ℝ => C * L ^ p) atTop atTop :=
    tendsto_weyl_main_term hC hp
  have hmul :
      Tendsto (fun L : ℝ => (C * L ^ p) * ((counting S L : ℝ) / (C * L ^ p)))
        atTop atTop :=
    Filter.Tendsto.atTop_mul_pos one_pos hmain hratio
  exact hmul.congr' (eventuallyEq_counting_mul_ratio S hC)

/-- A spectrum satisfying a Weyl law is infinite. -/
theorem infinite_of_discrete_and_WeylLawMatch
    (S : Set ℝ) (C p : ℝ) (hdisc : Discrete S) (hW : WeylLawMatch S C p) :
    S.Infinite := by
  intro hfin
  have hdiv := counting_diverges_of_discrete_and_WeylLawMatch S C p hdisc hW
  obtain ⟨L, hL⟩ := (hdiv.eventually_ge_atTop ((S.ncard : ℝ) + 1)).exists
  have hbound : counting S L ≤ S.ncard :=
    Set.ncard_le_ncard Set.inter_subset_left hfin
  have hbound' : ((counting S L : ℝ)) ≤ (S.ncard : ℝ) := by exact_mod_cast hbound
  linarith

/-!
## Non-vacuity

The hypotheses above are satisfiable: the spectrum `S = ℕ ⊆ ℝ` is discrete and matches
the Weyl law with `C = 1`, `p = 1`.
-/

/-- Counting function of the model spectrum `ℕ ⊆ ℝ`: for `Λ ≥ 0` it equals `⌊Λ⌋ + 1`. -/
lemma natSpectrum_counting (L : ℝ) (hL : 0 ≤ L) :
    counting (Set.range ((↑) : ℕ → ℝ)) L = ⌊L⌋₊ + 1 := by
  have hset : (Set.range ((↑) : ℕ → ℝ)) ∩ Set.Iic L
      = ((Finset.range (⌊L⌋₊ + 1)).image (fun n : ℕ => (n : ℝ)) : Finset ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_Iic, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩
      exact ⟨n, Nat.lt_succ_of_le (Nat.le_floor hx), rfl⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, ?_⟩
      have hn' : n ≤ ⌊L⌋₊ := Nat.lt_succ_iff.mp hn
      calc (n : ℝ) ≤ (⌊L⌋₊ : ℝ) := by exact_mod_cast hn'
        _ ≤ L := Nat.floor_le hL
  rw [counting, hset, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- The model spectrum `ℕ ⊆ ℝ` is discrete. -/
lemma natSpectrum_discrete : Discrete (Set.range ((↑) : ℕ → ℝ)) := by
  intro L
  refine Set.Finite.subset
    (((Finset.range (⌊L⌋₊ + 1)).image (fun n : ℕ => (n : ℝ))).finite_toSet) ?_
  rintro x ⟨⟨n, rfl⟩, hx⟩
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  exact ⟨n, Nat.lt_succ_of_le (Nat.le_floor hx), rfl⟩

/-- The model spectrum `ℕ ⊆ ℝ` matches the Weyl law with `C = 1` and `p = 1`. -/
lemma natSpectrum_weylLawMatch : WeylLawMatch (Set.range ((↑) : ℕ → ℝ)) 1 1 := by
  refine ⟨one_pos, one_pos, ?_⟩
  have hlow : ∀ᶠ L : ℝ in atTop,
      (1 : ℝ) ≤ (counting (Set.range ((↑) : ℕ → ℝ)) L : ℝ) / (1 * L ^ (1 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [natSpectrum_counting L hL.le, Real.rpow_one, one_mul, le_div_iff₀ hL]
    push_cast
    have := Nat.lt_floor_add_one L
    linarith
  have hup : ∀ᶠ L : ℝ in atTop,
      (counting (Set.range ((↑) : ℕ → ℝ)) L : ℝ) / (1 * L ^ (1 : ℝ)) ≤ 1 + 1 / L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [natSpectrum_counting L hL.le, Real.rpow_one, one_mul, div_le_iff₀ hL]
    push_cast
    have := Nat.floor_le hL.le
    field_simp
    linarith
  have h1 : Tendsto (fun L : ℝ => 1 + 1 / L) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).add
      tendsto_inv_atTop_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 hlow hup

/-- Instance of the main theorem on the model spectrum `ℕ ⊆ ℝ`. -/
example : Tendsto (fun L : ℝ => (counting (Set.range ((↑) : ℕ → ℝ)) L : ℝ)) atTop atTop :=
  counting_diverges_of_discrete_and_WeylLawMatch _ 1 1 natSpectrum_discrete
    natSpectrum_weylLawMatch

end Brockian.Weyl.WeylLawTarget

