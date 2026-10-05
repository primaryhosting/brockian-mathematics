/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real

namespace Phys

/-- The spin-wave (harmonic) energy of the Fourier mode `j` of a nearest-neighbour
model on the `d`-dimensional discrete torus with `L` sites per side, in units where
the coupling constant is `1`.  The momentum attached to the mode `j` has components
`k i = 2π * j i / L`, and the lattice dispersion relation is
`ε k = ∑ i, 2 * (1 - cos (k i))`. -/
noncomputable def spinWaveEnergy (d L : ℕ) (j : Fin d → Fin L) : ℝ :=
  ∑ i, 2 * (1 - Real.cos (2 * π * ((j i : ℕ) : ℝ) / (L : ℝ)))

/-- The squared momentum `|k|² = ∑ i, (2π * j i / L)²` of the Fourier mode `j`. -/
noncomputable def modeSq (d L : ℕ) (j : Fin d → Fin L) : ℝ :=
  ∑ i, (2 * π * ((j i : ℕ) : ℝ) / (L : ℝ)) ^ 2

/-- The lattice dispersion relation is dominated by the continuum one: `ε k ≤ |k|²`. -/
lemma spinWaveEnergy_le_modeSq (d L : ℕ) (j : Fin d → Fin L) :
    spinWaveEnergy d L j ≤ modeSq d L j := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Real.one_sub_sq_div_two_le_cos (x := 2 * π * ((j i : ℕ) : ℝ) / (L : ℝ))
  linarith

/-- A nonzero mode has strictly positive squared momentum. -/
lemma modeSq_pos {d L : ℕ} {j : Fin d → Fin L} (hj : ∃ i, (j i : ℕ) ≠ 0) :
    0 < modeSq d L j := by
  obtain ⟨i, hi⟩ := hj
  have hL : (0:ℝ) < (L:ℝ) := by exact_mod_cast (j i).pos
  have h1 : (0:ℝ) < ((j i : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  positivity

/-- In one dimension the sum `∑_{k ≠ 0} |k|⁻²` over the Brillouin zone grows faster
than the volume `L`. -/
lemma exists_mode_sum_gt_one (B : ℝ) :
    ∃ (L : ℕ) (D : Finset (Fin 1 → Fin L)),
      (∀ j ∈ D, ∃ i, (j i : ℕ) ≠ 0) ∧
      B * (L : ℝ) ^ (1 : ℕ) < ∑ j ∈ D, 1 / modeSq 1 L j := by
  set L : ℕ := ⌈4 * π ^ 2 * B⌉₊ + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have hLR : (0:ℝ) < (L:ℝ) := by positivity
  have hBL : 4 * π ^ 2 * B < (L:ℝ) := by
    have h1 : ((⌈4 * π ^ 2 * B⌉₊ : ℕ) : ℝ) + 2 = (L:ℝ) := by
      rw [hL]; push_cast; ring
    linarith [Nat.le_ceil (4 * π ^ 2 * B)]
  refine ⟨L, {fun _ => (⟨1, by omega⟩ : Fin L)}, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    refine ⟨0, ?_⟩
    simp [hj]
    omega
  · rw [Finset.sum_singleton]
    have hq : modeSq 1 L (fun _ => (⟨1, by omega⟩ : Fin L)) = 4 * π ^ 2 / (L:ℝ) ^ 2 := by
      simp [modeSq]
      ring
    rw [hq, one_div_div, pow_one, lt_div_iff₀ (by positivity)]
    nlinarith [hLR, hBL, Real.pi_pos]

/-- Rewriting a sum over the "triangular" set of two-dimensional modes
`{0 < j 0 ≤ j 1}` as an iterated sum. -/
lemma sum_filter_tri (L : ℕ) [NeZero L] (F : (Fin 2 → Fin L) → ℝ) :
    ∑ j ∈ (Finset.univ.filter
        (fun j : Fin 2 → Fin L => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ))), F j
      = ∑ b : Fin L, ∑ a : Fin L, (if 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ) then F ![a, b] else 0) := by
  rw [Finset.sum_filter, ← Equiv.sum_comp (piFinTwoEquiv (fun _ => Fin L)).symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  congr 1

/-- There are exactly `b` indices `a` with `0 < a ≤ b`. -/
lemma sum_ite_Ioc (L : ℕ) [NeZero L] (b : Fin L) (c : ℝ) :
    ∑ a : Fin L, (if 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ) then c else 0) = (b:ℕ) * c := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  have h : (Finset.univ.filter (fun a : Fin L => 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ)))
      = Finset.Ioc 0 b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc,
      Fin.lt_def, Fin.le_def, Fin.val_zero]
  rw [h, Fin.card_Ioc]
  simp

/-- In two dimensions the sum `∑_{k ≠ 0} |k|⁻²` over the Brillouin zone grows faster
than the volume `L²`: this is the logarithmic infrared divergence responsible for the
Mermin–Wagner theorem in the critical dimension. -/
lemma exists_mode_sum_gt_two (B : ℝ) :
    ∃ (L : ℕ) (D : Finset (Fin 2 → Fin L)),
      (∀ j ∈ D, ∃ i, (j i : ℕ) ≠ 0) ∧
      B * (L : ℝ) ^ (2 : ℕ) < ∑ j ∈ D, 1 / modeSq 2 L j := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 8 * π ^ 2 * B < ∑ i ∈ Finset.range N, 1 / ((i:ℝ) + 1) :=
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (8 * π ^ 2 * B)).exists
  refine ⟨N + 1,
    Finset.univ.filter (fun j : Fin 2 → Fin (N+1) => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)),
    ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_filter] at hj
    exact ⟨0, by omega⟩
  · set L : ℕ := N + 1 with hLdef
    have hLR : (0:ℝ) < (L:ℝ) := by positivity
    have hpt : ∀ j ∈ Finset.univ.filter
        (fun j : Fin 2 → Fin L => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)),
        (L:ℝ)^2 / (8 * π^2) * (1 / ((j 1 : ℕ):ℝ)^2) ≤ 1 / modeSq 2 L j := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨h0, h1⟩ := hj
      have hb : (0:ℝ) < ((j 1 : ℕ):ℝ) := by
        have : 0 < (j 1 : ℕ) := lt_of_lt_of_le h0 h1
        exact_mod_cast this
      have ha : (0:ℝ) ≤ ((j 0 : ℕ):ℝ) := by positivity
      have hab : ((j 0 : ℕ):ℝ) ≤ ((j 1 : ℕ):ℝ) := by exact_mod_cast h1
      have hQpos : 0 < modeSq 2 L j := modeSq_pos ⟨0, by omega⟩
      have ha2 : ((j 0 : ℕ):ℝ)^2 ≤ ((j 1 : ℕ):ℝ)^2 := by nlinarith
      have hQle : modeSq 2 L j ≤ 8 * π^2 * ((j 1 : ℕ):ℝ)^2 / (L:ℝ)^2 := by
        rw [modeSq, Fin.sum_univ_two, div_pow, div_pow, ← add_div,
          div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [Real.pi_pos, sq_nonneg π, mul_le_mul_of_nonneg_left ha2 (sq_nonneg π)]
      have hfin := one_div_le_one_div_of_le hQpos hQle
      calc (L:ℝ)^2 / (8 * π^2) * (1 / ((j 1 : ℕ):ℝ)^2)
          = 1 / (8 * π^2 * ((j 1 : ℕ):ℝ)^2 / (L:ℝ)^2) := by
            rw [one_div_div]; field_simp
        _ ≤ 1 / modeSq 2 L j := hfin
    refine lt_of_lt_of_le ?_ (Finset.sum_le_sum hpt)
    have hcomp : ∑ j ∈ Finset.univ.filter
        (fun j : Fin 2 → Fin L => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ)),
        (L:ℝ)^2 / (8 * π^2) * (1 / ((j 1 : ℕ):ℝ)^2)
        = (L:ℝ)^2 / (8 * π^2) * ∑ i ∈ Finset.range N, 1 / ((i:ℝ) + 1) := by
      rw [sum_filter_tri]
      have hb : ∀ b : Fin L, ∑ a : Fin L,
          (if 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ) then
            (L:ℝ)^2 / (8 * π^2) * (1 / (((![a, b] : Fin 2 → Fin L) 1 : ℕ):ℝ)^2) else 0)
          = (L:ℝ)^2 / (8 * π^2) * (1 / ((b:ℕ):ℝ)) := by
        intro b
        have hsimp : ∀ a : Fin L, (((![a, b] : Fin 2 → Fin L) 1 : ℕ):ℝ) = ((b:ℕ):ℝ) := by
          intro a; simp
        simp only [hsimp]
        rw [sum_ite_Ioc]
        rcases Nat.eq_zero_or_pos (b:ℕ) with h | h
        · simp [h]
        · have hbne : ((b:ℕ):ℝ) ≠ 0 := by positivity
          field_simp
      simp only [hb]
      rw [← Finset.mul_sum]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i => 1 / ((i:ℕ):ℝ)) L, hLdef, Finset.sum_range_succ']
      simp
    rw [hcomp, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hN (show (0:ℝ) < (L:ℝ)^2 by positivity)
    linarith

/-- Infrared divergence in dimension `d ≤ 2`: the sum of `|k|⁻²` over a set of
nonzero modes can be made arbitrarily large compared with the volume `L ^ d`. -/
lemma exists_mode_sum_gt (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (B : ℝ) :
    ∃ (L : ℕ) (D : Finset (Fin d → Fin L)),
      (∀ j ∈ D, ∃ i, (j i : ℕ) ≠ 0) ∧
      B * (L : ℝ) ^ d < ∑ j ∈ D, 1 / modeSq d L j := by
  interval_cases d
  · exact exists_mode_sum_gt_one B
  · exact exists_mode_sum_gt_two B

/--
**Mermin–Wagner theorem.**

There is no spontaneous breaking of a continuous symmetry at positive temperature in
dimension `d ≤ 2`.

The setting is a nearest-neighbour spin model with a continuous internal symmetry on
the `d`-dimensional discrete torus with `L` sites per side, at temperature `T > 0`.
`S L j` denotes the static structure factor (the thermal expectation `⟨|S k|²⟩` of the
squared transverse spin fluctuation) of the Fourier mode `j`, and `m` denotes the
spontaneous magnetisation of the symmetry-breaking order parameter.  The two physical
inputs are:

* the *sum rule* `∑ k, ⟨|S k|²⟩ ≤ L ^ d`, expressing that the spins have bounded
  length (normalised to `1`);
* the *Bogoliubov inequality* `T * m² ≤ 2 * C * ε k * ⟨|S k|²⟩` for every nonzero mode
  `k`, where `ε k` is the spin-wave energy and `C > 0` is a constant built from the
  interaction strength.

The conclusion is that the magnetisation vanishes, `m = 0`: the continuous symmetry
cannot be spontaneously broken.  The mechanism is the infrared divergence of
`∑_{k ≠ 0} |k|⁻²` relative to the volume in dimensions `d ≤ 2`.
-/
theorem mermin_wagner
    {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d ≤ 2)
    {T C m : ℝ} (hT : 0 < T) (hC : 0 < C)
    (S : ∀ L : ℕ, (Fin d → Fin L) → ℝ)
    (hS0 : ∀ (L : ℕ) (j : Fin d → Fin L), 0 ≤ S L j)
    (hsum : ∀ L : ℕ, ∑ j, S L j ≤ (L : ℝ) ^ d)
    (hbog : ∀ (L : ℕ) (j : Fin d → Fin L), (∃ i, (j i : ℕ) ≠ 0) →
      T * m ^ 2 ≤ 2 * C * spinWaveEnergy d L j * S L j) :
    m = 0 := by
  by_contra hm
  have hm2 : 0 < m ^ 2 := by positivity
  have hapos : 0 < T * m ^ 2 / (2 * C) := by positivity
  obtain ⟨L, D, hDne, hDgt⟩ := exists_mode_sum_gt d hd1 hd2 (2 * C / (T * m ^ 2))
  have key : ∀ j ∈ D, (T * m ^ 2 / (2 * C)) * (1 / modeSq d L j) ≤ S L j := by
    intro j hj
    have hne := hDne j hj
    have hQ : 0 < modeSq d L j := modeSq_pos hne
    have hSj : 0 ≤ S L j := hS0 L j
    have h3 := spinWaveEnergy_le_modeSq d L j
    have h1 : T * m ^ 2 ≤ 2 * C * modeSq d L j * S L j := by
      refine le_trans (hbog L j hne) ?_
      have h4 : 2 * C * spinWaveEnergy d L j ≤ 2 * C * modeSq d L j := by nlinarith
      exact mul_le_mul_of_nonneg_right h4 hSj
    have heq : (T * m ^ 2 / (2 * C)) * (1 / modeSq d L j)
        = T * m ^ 2 / (2 * C * modeSq d L j) := by
      field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    nlinarith
  have h1 : (T * m ^ 2 / (2 * C)) * ∑ j ∈ D, 1 / modeSq d L j ≤ ∑ j ∈ D, S L j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum key
  have h2 : ∑ j ∈ D, S L j ≤ (L : ℝ) ^ d :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hS0 L i)) (hsum L)
  have h4 := mul_lt_mul_of_pos_left hDgt hapos
  have h5 : (T * m ^ 2 / (2 * C)) * ((2 * C / (T * m ^ 2)) * (L : ℝ) ^ d) = (L : ℝ) ^ d := by
    field_simp
  linarith

end Phys

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

