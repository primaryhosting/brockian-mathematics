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
