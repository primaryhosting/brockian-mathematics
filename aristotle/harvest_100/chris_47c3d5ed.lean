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

/-!
## Mermin–Wagner: absence of continuous symmetry breaking in dimensions `d ≤ 2`

The mechanism behind the Mermin–Wagner theorem is an *energy–entropy* (spin-wave) estimate.
In a lattice system with a continuous internal symmetry, a configuration may be deformed by a
slowly varying, *finitely supported* rotation field `u : ℤ^d → ℝ`; to second order (which is
the relevant order, the first order term vanishing by the symmetry `θ ↦ -θ`) the free-energy
cost of the deformation at temperature `T` and coupling `J` is

  `(J / (2T)) * ∑_{⟨x,y⟩} (u x - u y)^2`,

i.e. `J / (2T)` times the *Dirichlet energy* of `u`.  Spontaneous breaking of the continuous
symmetry requires this cost to stay bounded away from zero when a fixed finite region is
rotated by a fixed angle `α` and the rotation is relaxed back to `0` at infinity; this
infimum is (up to the factor `J / (2T)`) the *capacity* of the region.

The theorem `Phys.mermin_wagner` below is exactly the statement that in dimension `d ≤ 2`
this cost vanishes: for every temperature `T > 0`, every coupling `J > 0`, every finite
region `A`, every rotation angle `α` and every `ε > 0`, there is a finitely supported
rotation field which rotates all of `A` by the full angle `α` at a free-energy cost less
than `ε`.  Equivalently: finite subsets of `ℤ^d` have zero capacity for `d ≤ 2` (`ℤ^d` is
recurrent/parabolic), so no continuous symmetry can be broken at any positive temperature.

The dimension enters through the divergence of the harmonic series: the shells
`{x : ‖x‖_∞ = s}` of `ℤ^d` with `d ≤ 2` contain `O(s)` points, so the harmonic profile
`u x = φ(‖x‖_∞)` used below has Dirichlet energy `O(1 / ∑_{s ≤ N} 1/s) → 0`.  In dimension
`d ≥ 3` shells contain `≍ s^{d-1}` points, the estimate fails, and indeed symmetry breaking
does occur.
-/

namespace Phys

variable {d : ℕ}

/-- The `i`-th unit vector of the lattice `ℤ^d`. -/
def unitVec (i : Fin d) : Fin d → ℤ := fun j => if j = i then 1 else 0

/-- The sup-norm `‖x‖_∞` of a lattice point, as a natural number. -/
def normInf (x : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The Dirichlet (spin-wave) energy `∑_{⟨x,y⟩} (u x - u y)^2` of a rotation field
`u : ℤ^d → ℝ`, the sum running over all nearest-neighbour bonds of `ℤ^d`. -/
noncomputable def dirichlet (u : (Fin d → ℤ) → ℝ) : ℝ :=
  ∑' x : Fin d → ℤ, ∑ i : Fin d, (u (x + unitVec i) - u x) ^ 2

/-- The box `{x : ‖x‖_∞ ≤ M}` of `ℤ^d`. -/
def box (M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- Partial sums of the harmonic series. -/
noncomputable def harm (s : ℕ) : ℝ := ∑ t ∈ Finset.range s, (1 : ℝ) / (t + 1)

/-! ### Basic properties of `normInf` and `box` -/

lemma normInf_le_iff {M : ℕ} {x : Fin d → ℤ} :
    normInf x ≤ M ↔ ∀ i, (x i).natAbs ≤ M := by
  simp [normInf, Finset.sup_le_iff]

lemma natAbs_le_normInf (x : Fin d → ℤ) (i : Fin d) : (x i).natAbs ≤ normInf x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

lemma mem_box {M : ℕ} {x : Fin d → ℤ} : x ∈ (box M : Finset (Fin d → ℤ)) ↔ normInf x ≤ M := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, normInf_le_iff]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

lemma normInf_add_le (x y : Fin d → ℤ) : normInf (x + y) ≤ normInf x + normInf y := by
  rw [normInf_le_iff]
  intro i
  have h : ((x + y) i).natAbs ≤ (x i).natAbs + (y i).natAbs := by
    simpa using Int.natAbs_add_le (x i) (y i)
  exact h.trans (Nat.add_le_add (natAbs_le_normInf x i) (natAbs_le_normInf y i))

lemma normInf_unitVec_le (i : Fin d) : normInf (unitVec i) ≤ 1 := by
  rw [normInf_le_iff]
  intro j
  by_cases h : j = i <;> simp [unitVec, h]

lemma normInf_neg (x : Fin d → ℤ) : normInf (-x) = normInf x := by
  simp [normInf]

lemma normInf_add_unitVec_le (x : Fin d → ℤ) (i : Fin d) :
    normInf (x + unitVec i) ≤ normInf x + 1 :=
  (normInf_add_le x _).trans (Nat.add_le_add_left (normInf_unitVec_le i) _)

lemma normInf_le_add_unitVec (x : Fin d → ℤ) (i : Fin d) :
    normInf x ≤ normInf (x + unitVec i) + 1 := by
  have h : x = (x + unitVec i) + (-unitVec i) := by simp
  calc normInf x ≤ normInf (x + unitVec i) + normInf (-unitVec i) := by
        conv_lhs => rw [h]
        exact normInf_add_le _ _
    _ ≤ normInf (x + unitVec i) + 1 := by
        rw [normInf_neg]
        exact Nat.add_le_add_left (normInf_unitVec_le i) _

lemma card_box (M : ℕ) : (box M : Finset (Fin d → ℤ)).card = (2 * M + 1) ^ d := by
  classical
  rw [box, Fintype.card_piFinset]
  have h : ∀ i : Fin d, (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl (fun i _ => h i)]
  simp

lemma box_subset {M N : ℕ} (h : M ≤ N) :
    (box M : Finset (Fin d → ℤ)) ⊆ (box N : Finset (Fin d → ℤ)) := by
  intro x hx
  exact mem_box.2 ((mem_box.1 hx).trans h)

/-- In dimension `d ≤ 2` the sup-norm sphere of radius `s ≥ 1` contains at most `12 s`
lattice points.  (This linear growth of the shells is what makes `d ≤ 2` special.) -/
lemma card_shell_le (hd : d ≤ 2) {s : ℕ} (hs : 1 ≤ s) :
    (((box s : Finset (Fin d → ℤ))).filter (fun x => normInf x = s)).card ≤ 12 * s := by
  classical
  have hsub : ((box s : Finset (Fin d → ℤ))).filter (fun x => normInf x = s) ⊆
      (box s : Finset (Fin d → ℤ)) \ (box (s - 1) : Finset (Fin d → ℤ)) := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    refine Finset.mem_sdiff.2 ⟨hx.1, ?_⟩
    intro hmem
    have := mem_box.1 hmem
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (box_subset (show s - 1 ≤ s by omega)), card_box, card_box]
    at hcard
  refine hcard.trans ?_
  interval_cases d
  · simp
  · simp; omega
  · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega

/-! ### Harmonic sums -/

lemma harm_succ (s : ℕ) : harm (s + 1) = harm s + 1 / (s + 1) :=
  Finset.sum_range_succ _ _

lemma harm_mono : Monotone harm := by
  intro a b hab
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hab)) ?_
  intro i _ _
  positivity

lemma harm_nonneg (s : ℕ) : 0 ≤ harm s := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- Two harmonic partial sums with indices at distance at most one differ by at most `1/k`. -/
lemma abs_harm_sub_le {k m : ℕ} (hk : 1 ≤ k) (h1 : m ≤ k + 1) (h2 : k ≤ m + 1) :
    |harm m - harm k| ≤ 1 / (k : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hcase : m = j ∨ m = j + 1 ∨ m = j + 2 := by omega
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rcases hcase with rfl | rfl | rfl
  · rw [harm_succ]
    have h : harm m - (harm m + 1 / ((m : ℝ) + 1)) = -(1 / ((m : ℝ) + 1)) := by ring
    rw [h, abs_neg, abs_of_nonneg (by positivity)]
    push_cast
    exact le_refl _
  · simp
    positivity
  · rw [show j + 2 = (j + 1) + 1 from rfl, harm_succ (j + 1)]
    have h : harm (j + 1) + 1 / (((j : ℕ) + 1 : ℕ) + 1 : ℝ) - harm (j + 1)
        = 1 / ((j : ℝ) + 2) := by push_cast; ring
    rw [h, abs_of_nonneg (by positivity)]
    push_cast
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith

/-! ### The key counting estimate -/

/-- In dimension `d ≤ 2`, `∑_{0 < ‖x‖_∞ ≤ M} ‖x‖_∞^{-2}` grows only like the harmonic sum. -/
lemma sum_inv_sq_le (hd : d ≤ 2) (M : ℕ) :
    ∑ x ∈ (box M : Finset (Fin d → ℤ)),
        (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2) ≤ 12 * harm M := by
  classical
  have hmaps : ∀ x ∈ (box M : Finset (Fin d → ℤ)), normInf x ∈ Finset.range (M + 1) := by
    intro x hx
    have := mem_box.1 hx
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ s ∈ Finset.range (M + 1),
      (∑ x ∈ (box M : Finset (Fin d → ℤ)) with normInf x = s,
        (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2))
        ≤ (if s = 0 then (0 : ℝ) else 12 / (s : ℝ)) := by
    intro s _
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [if_pos rfl]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [if_pos hx.2]
    · have hconst : (∑ x ∈ (box M : Finset (Fin d → ℤ)) with normInf x = s,
          (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2))
          = (((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)).card : ℝ)
              * (1 / (s : ℝ) ^ 2) := by
        rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.mem_filter] at hx
        rw [hx.2, if_neg (by omega)]
      rw [hconst, if_neg (by omega)]
      have hcard : (((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)).card : ℝ)
          ≤ 12 * (s : ℝ) := by
        have hsub : ((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)) ⊆
            ((box s : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)) := by
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨mem_box.2 (le_of_eq hx.2), hx.2⟩
        have h := (Finset.card_le_card hsub).trans (card_shell_le hd hs)
        exact_mod_cast h
      have hspos : (0 : ℝ) < s := by exact_mod_cast hs
      calc (((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)).card : ℝ)
            * (1 / (s : ℝ) ^ 2) ≤ (12 * (s : ℝ)) * (1 / (s : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 12 / (s : ℝ) := by field_simp
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range M,
      (if i + 1 = 0 then (0 : ℝ) else 12 / ((i + 1 : ℕ) : ℝ)) = 12 * (1 / ((i : ℝ) + 1)) := by
    intro i _
    rw [if_neg (by omega)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hz, ← Finset.mul_sum, if_pos rfl, add_zero]
  rfl

/-! ### Elementary properties of the Dirichlet energy -/

lemma dirichlet_nonneg (u : (Fin d → ℤ) → ℝ) : 0 ≤ dirichlet u :=
  tsum_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma dirichlet_smul (α : ℝ) (u : (Fin d → ℤ) → ℝ) :
    dirichlet (fun x => α * u x) = α ^ 2 * dirichlet u := by
  simp only [dirichlet]
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The key estimate: finite sets have arbitrarily small capacity when `d ≤ 2` -/

/-- **Key estimate (zero capacity in `d ≤ 2`).**  In dimension `d ≤ 2`, every finite region
`A ⊆ ℤ^d` carries a finitely supported field which equals `1` on `A` and has arbitrarily
small Dirichlet energy.  Equivalently, finite subsets of `ℤ^d` have zero capacity, i.e. the
simple random walk on `ℤ^d` is recurrent for `d ≤ 2`. -/
theorem exists_dirichlet_lt (hd : d ≤ 2) (A : Finset (Fin d → ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : (Fin d → ℤ) → ℝ,
      (Function.support u).Finite ∧ (∀ x ∈ A, u x = 1) ∧ dirichlet u < ε := by
  classical
  set n : ℕ := A.sup normInf + 1 with hn
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max (2 * harm n) (96 / ε) < harm N := by
    have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
    exact (h.eventually_gt_atTop (max (2 * harm n) (96 / ε))).exists
  have hN1 : 2 * harm n < harm N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 96 / ε < harm N := lt_of_le_of_lt (le_max_right _ _) hN
  have hharmN : 0 < harm N := lt_of_le_of_lt (by positivity) hN2
  set D : ℝ := harm N - harm n with hDdef
  have hD : harm N / 2 < D := by
    have := harm_nonneg n
    simp only [hDdef]
    linarith
  have hDpos : 0 < D := lt_trans (by linarith) hD
  -- the harmonic cut-off profile
  set g : ℕ → ℝ := fun s => max 0 (min 1 ((harm N - harm s) / D)) with hgdef
  have hg1 : ∀ s : ℕ, s ≤ n → g s = 1 := by
    intro s hs
    have hh : harm s ≤ harm n := harm_mono hs
    have hge : 1 ≤ (harm N - harm s) / D := by
      rw [le_div_iff₀ hDpos]
      simp only [hDdef]
      linarith
    simp only [hgdef]
    rw [min_eq_left hge, max_eq_right zero_le_one]
  have hg0 : ∀ s : ℕ, N ≤ s → g s = 0 := by
    intro s hs
    have hh : harm N ≤ harm s := harm_mono hs
    have hq : (harm N - harm s) / D ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hDpos.le
    simp only [hgdef]
    rw [min_eq_right (by linarith), max_eq_left hq]
  have hlip : ∀ s t : ℕ, |g s - g t| ≤ |harm s - harm t| / D := by
    intro s t
    have key : |max 0 (min 1 ((harm N - harm s) / D)) - max 0 (min 1 ((harm N - harm t) / D))|
        ≤ |(harm N - harm s) / D - (harm N - harm t) / D| := by
      set a := (harm N - harm s) / D
      set b := (harm N - harm t) / D
      rw [abs_le, max_def, max_def, min_def, min_def]
      split_ifs <;> constructor <;>
        linarith [le_abs_self (a - b), neg_abs_le (a - b), abs_nonneg (a - b)]
    have heq : |(harm N - harm s) / D - (harm N - harm t) / D| = |harm s - harm t| / D := by
      rw [div_sub_div_same, abs_div, abs_of_pos hDpos]
      congr 1
      rw [show harm N - harm s - (harm N - harm t) = -(harm s - harm t) by ring, abs_neg]
    simp only [hgdef]
    exact heq ▸ key
  refine ⟨fun x => g (normInf x), ?_, ?_, ?_⟩
  · -- the profile has finite support
    apply Set.Finite.subset (box N : Finset (Fin d → ℤ)).finite_toSet
    intro x hx
    simp only [Function.mem_support] at hx
    have hlt : normInf x < N := by
      by_contra hcon
      push_neg at hcon
      exact hx (hg0 _ hcon)
    exact Finset.mem_coe.2 (mem_box.2 hlt.le)
  · -- the profile equals `1` on `A`
    intro x hxA
    have hle : normInf x ≤ n := by
      have : normInf x ≤ A.sup normInf := Finset.le_sup hxA
      omega
    exact hg1 _ hle
  · -- the Dirichlet energy of the profile is small
    have hterm : ∀ (x : Fin d → ℤ) (i : Fin d),
        (g (normInf (x + unitVec i)) - g (normInf x)) ^ 2
          ≤ (1 / D ^ 2) * (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2) := by
      intro x i
      rcases Nat.eq_zero_or_pos (normInf x) with h0 | hpos
      · rw [if_pos h0]
        have h1 : normInf (x + unitVec i) ≤ n := by
          have := normInf_add_unitVec_le x i
          omega
        rw [hg1 _ h1, hg1 _ (by omega : normInf x ≤ n)]
        simp
      · rw [if_neg (by omega)]
        have hb1 : normInf (x + unitVec i) ≤ normInf x + 1 := normInf_add_unitVec_le x i
        have hb2 : normInf x ≤ normInf (x + unitVec i) + 1 := normInf_le_add_unitVec x i
        have hkpos : (0 : ℝ) < (normInf x : ℝ) := by exact_mod_cast hpos
        have habs : |g (normInf (x + unitVec i)) - g (normInf x)| ≤ (1 / (normInf x : ℝ)) / D := by
          refine (hlip _ _).trans ?_
          have h := abs_harm_sub_le hpos hb1 hb2
          gcongr
        calc (g (normInf (x + unitVec i)) - g (normInf x)) ^ 2
            = |g (normInf (x + unitVec i)) - g (normInf x)| ^ 2 := (sq_abs _).symm
          _ ≤ ((1 / (normInf x : ℝ)) / D) ^ 2 := by gcongr
          _ = (1 / D ^ 2) * (1 / (normInf x : ℝ) ^ 2) := by field_simp
    set gg : (Fin d → ℤ) → ℝ :=
      fun x => (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2) with hggdef
    have hggnn : ∀ x, 0 ≤ gg x := by
      intro x
      simp only [hggdef]
      split_ifs
      · exact le_refl 0
      · positivity
    have hFbound : ∀ x : Fin d → ℤ,
        ∑ i : Fin d, (g (normInf (x + unitVec i)) - g (normInf x)) ^ 2
          ≤ 2 * ((1 / D ^ 2) * gg x) := by
      intro x
      calc ∑ i : Fin d, (g (normInf (x + unitVec i)) - g (normInf x)) ^ 2
          ≤ ∑ _i : Fin d, ((1 / D ^ 2) * gg x) := Finset.sum_le_sum (fun i _ => hterm x i)
        _ = (d : ℝ) * ((1 / D ^ 2) * gg x) := by simp [Finset.sum_const]
        _ ≤ 2 * ((1 / D ^ 2) * gg x) := by
            have hd' : (d : ℝ) ≤ 2 := by exact_mod_cast hd
            have hc : 0 ≤ (1 / D ^ 2) * gg x := mul_nonneg (by positivity) (hggnn x)
            nlinarith
    have hvanish : ∀ x ∉ (box N : Finset (Fin d → ℤ)),
        ∑ i : Fin d,
          ((fun x => g (normInf x)) (x + unitVec i) - (fun x => g (normInf x)) x) ^ 2 = 0 := by
      intro x hx
      have hxN : N < normInf x := by
        by_contra h
        exact hx (mem_box.2 (by omega))
      apply Finset.sum_eq_zero
      intro i _
      have h1 : N ≤ normInf (x + unitVec i) := by
        have := normInf_le_add_unitVec x i
        omega
      simp only
      rw [hg0 _ h1, hg0 _ (by omega)]
      ring
    have hsum : dirichlet (d := d) (fun x => g (normInf x))
        = ∑ x ∈ (box N : Finset (Fin d → ℤ)),
            ∑ i : Fin d, (g (normInf (x + unitVec i)) - g (normInf x)) ^ 2 := by
      simp only [dirichlet]
      exact tsum_eq_sum hvanish
    rw [hsum]
    have h1 : ∑ x ∈ (box N : Finset (Fin d → ℤ)),
        ∑ i : Fin d, (g (normInf (x + unitVec i)) - g (normInf x)) ^ 2
        ≤ ∑ x ∈ (box N : Finset (Fin d → ℤ)), 2 * ((1 / D ^ 2) * gg x) :=
      Finset.sum_le_sum (fun x _ => hFbound x)
    have h2 : ∑ x ∈ (box N : Finset (Fin d → ℤ)), 2 * ((1 / D ^ 2) * gg x)
        = (2 / D ^ 2) * ∑ x ∈ (box N : Finset (Fin d → ℤ)), gg x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have h3 : ∑ x ∈ (box N : Finset (Fin d → ℤ)), gg x ≤ 12 * harm N := sum_inv_sq_le hd N
    have h4 : (2 / D ^ 2) * ∑ x ∈ (box N : Finset (Fin d → ℤ)), gg x
        ≤ (2 / D ^ 2) * (12 * harm N) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (2 / D ^ 2) * (12 * harm N) < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have h96 : 96 < harm N * ε := by
        rw [div_lt_iff₀ hε] at hN2
        linarith
      nlinarith [sq_nonneg (D - harm N / 2), hharmN, hDpos]
    linarith

/-! ### Main theorem -/

/-- **Mermin–Wagner theorem (spin-wave / capacity form).**
In dimension `d ≤ 2`, at any positive temperature `T > 0` and any coupling strength `J > 0`,
a continuous symmetry cannot be spontaneously broken: for any finite region `A ⊆ ℤ^d`, any
rotation angle `α` and any `ε > 0`, there exists a *finitely supported* rotation field `u`
which rotates every site of `A` by the full angle `α`, and whose spin-wave free-energy cost
`J / (2T) * ∑_{⟨x,y⟩} (u x - u y)^2` is smaller than `ε`.

Thus the free-energy cost of a global rotation of an arbitrary finite region is zero at every
positive temperature, and no long-range order with respect to the continuous symmetry can
survive. -/
theorem mermin_wagner {d : ℕ} (hd : d ≤ 2) {T J : ℝ} (hT : 0 < T) (hJ : 0 < J)
    (α : ℝ) (A : Finset (Fin d → ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : (Fin d → ℤ) → ℝ,
      (Function.support u).Finite ∧ (∀ x ∈ A, u x = α) ∧
        J / (2 * T) * dirichlet u < ε := by
  have hc : 0 < J / (2 * T) := by positivity
  have hpos : 0 < J / (2 * T) * (α ^ 2 + 1) := by positivity
  obtain ⟨u₀, hfin, hone, hlt⟩ :=
    exists_dirichlet_lt hd A (ε := ε / (J / (2 * T) * (α ^ 2 + 1))) (by positivity)
  refine ⟨fun x => α * u₀ x, ?_, ?_, ?_⟩
  · exact hfin.subset (Function.support_mul_subset_right _ _)
  · intro x hx
    show α * u₀ x = α
    rw [hone x hx, mul_one]
  · rw [dirichlet_smul]
    have hnn : 0 ≤ dirichlet u₀ := dirichlet_nonneg u₀
    have h1 : J / (2 * T) * (α ^ 2 * dirichlet u₀)
        ≤ J / (2 * T) * ((α ^ 2 + 1) * dirichlet u₀) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      nlinarith
    have h2 : J / (2 * T) * ((α ^ 2 + 1) * dirichlet u₀) < ε := by
      calc J / (2 * T) * ((α ^ 2 + 1) * dirichlet u₀)
          = (J / (2 * T) * (α ^ 2 + 1)) * dirichlet u₀ := by ring
        _ < (J / (2 * T) * (α ^ 2 + 1)) * (ε / (J / (2 * T) * (α ^ 2 + 1))) :=
            mul_lt_mul_of_pos_left hlt hpos
        _ = ε := by field_simp
    linarith

/-- **Mermin–Wagner theorem, capacity form.**  In dimension `d ≤ 2` and at any positive
temperature, the infimum of the spin-wave free-energy cost of rotating a finite region `A`
by a fixed angle `α`, over all finitely supported rotation fields, is exactly `0`. -/
theorem mermin_wagner_sInf_cost_eq_zero {d : ℕ} (hd : d ≤ 2) {T J : ℝ} (hT : 0 < T) (hJ : 0 < J)
    (α : ℝ) (A : Finset (Fin d → ℤ)) :
    sInf {r : ℝ | ∃ u : (Fin d → ℤ) → ℝ,
      (Function.support u).Finite ∧ (∀ x ∈ A, u x = α) ∧ r = J / (2 * T) * dirichlet u} = 0 := by
  set S : Set ℝ := {r : ℝ | ∃ u : (Fin d → ℤ) → ℝ,
    (Function.support u).Finite ∧ (∀ x ∈ A, u x = α) ∧ r = J / (2 * T) * dirichlet u} with hS
  have hc : 0 < J / (2 * T) := by positivity
  have hnonneg : ∀ r ∈ S, 0 ≤ r := by
    rintro r ⟨u, -, -, rfl⟩
    exact mul_nonneg hc.le (dirichlet_nonneg u)
  have hne : S.Nonempty := by
    obtain ⟨u, hfin, hval, -⟩ := mermin_wagner hd hT hJ α A (ε := 1) one_pos
    exact ⟨J / (2 * T) * dirichlet u, ⟨u, hfin, hval, rfl⟩⟩
  have hbdd : BddBelow S := ⟨0, hnonneg⟩
  refine le_antisymm ?_ (le_csInf hne hnonneg)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨u, hfin, hval, hlt⟩ := mermin_wagner hd hT hJ α A hε
  have hmem : J / (2 * T) * dirichlet u ∈ S := ⟨u, hfin, hval, rfl⟩
  have := csInf_le hbdd hmem
  linarith

end Phys

