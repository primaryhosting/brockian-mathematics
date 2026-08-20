import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_ankeny_representation_q1 (n q : ℕ) (b : ℤ)
    (hn_pos : 0 < n) (hq : Nat.Prime q)
    (hnq : Nat.Coprime n q)
    (_hq1 : q % 4 = 1)
    (hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)]) :
    ∃ x y z : ℤ,
      ankeny_Q1 n q x y z = n * q ∧
      (x, y, z) ≠ (0, 0, 0) ∧
      x ≡ y [ZMOD (n : ℤ)] ∧
      y ≡ b * z [ZMOD (q : ℤ)] := by
  classical
  -- The same diagonal-map ellipsoid, but with smaller radius `sqrt(2*n*q)`.
  let ell (nR qR : ℝ) : Set E3 := ankenyEllipsoidL2_q1 nR qR

  have hq_pos : 0 < q := hq.pos

  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos

  -- Lattice + fundamental domain: use the explicit span lattice so `Countable ↥L` is available.
  let L : AddSubgroup E3 := ankeny_span_lattice_q1 n q b hn_pos hq_pos
  let F : Set E3 := ankeny_span_fundamentalDomain_q1 n q b hn_pos hq_pos

  letI : Countable (↥L) := by
    change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis_q1 n q b hn_pos hq_pos)))
    infer_instance

  have hfund : IsAddFundamentalDomain L F volume := by
    simpa [L, F] using ankeny_span_isAddFundamentalDomain_q1 n q b hn_pos hq_pos

  have hvolF : volume F = (n * q : ℝ≥0∞) := by
    simpa [F] using ankeny_span_volume_fundamentalDomain_q1 n q b hn_pos hq_pos

  -- Symmetry: `x ∈ ell → -x ∈ ell`.
  have hsymm : ∀ x ∈ ell (n : ℝ) (q : ℝ), -x ∈ ell (n : ℝ) (q : ℝ) := by
    intro x hx
    dsimp [ell, ankenyEllipsoidL2_q1, l2Ball] at hx ⊢
    simpa [Metric.mem_ball, map_neg, dist_eq_norm, norm_neg] using hx

  -- Convexity: preimage of a convex ball under an affine map.
  have hconv : Convex ℝ (ell (n : ℝ) (q : ℝ)) := by
    let toLpLin : E3 →ₗ[ℝ] E3L2 :=
      (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ E3).symm.toLinearMap
    let f : E3 →ᵃ[ℝ] E3L2 :=
      toLpLin.toAffineMap.comp (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ)).toAffineMap
    have hs :
        ell (n : ℝ) (q : ℝ) =
          f ⁻¹' Metric.ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) := by
      ext x
      rfl
    simpa [hs, ell, ankenyEllipsoidL2_q1, l2Ball, f, toLpLin] using
      (Convex.affine_preimage
        (f := f)
        (s := Metric.ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)))
        (convex_ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ))))

  -- `finrank E3 = 3`.
  have hrank : Module.finrank ℝ E3 = 3 := by simp [E3]

  have hineq :
      volume F * 2 ^ (Module.finrank ℝ E3) < volume (ell (n : ℝ) (q : ℝ)) := by
    have hL : volume F * 2 ^ (Module.finrank ℝ E3) = (8 * n * q : ℝ≥0∞) := by
      simp [hvolF, hrank, pow_succ, mul_left_comm, mul_comm]
      ring
    have hR : (8 * n * q : ℝ≥0∞) < volume (ell (n : ℝ) (q : ℝ)) := by
      simpa [ell] using volume_ankenyEllipsoidL2_q1_gt_nat (n := n) (q := q) hn_pos hq_pos
    calc
      volume F * 2 ^ (Module.finrank ℝ E3) = (8 * n * q : ℝ≥0∞) := hL
      _ < volume (ell (n : ℝ) (q : ℝ)) := hR

  rcases
      GeometryOfNumbers.minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
        (μ := volume) (L := L) (F := F) (s := ell (n : ℝ) (q : ℝ))
        hfund hsymm hconv hineq
    with ⟨p, hp0, hp_mem⟩

  -- Convert `p ∈ L` into explicit integer coordinates via the congruence-defined lattice.
  have hpL : ((p : E3) ∈ L) := p.property
  have hp_ank : (p : E3) ∈ ankeny_lattice_q1 n q b := by
    have hsub := ankeny_span_lattice_q1_subset_ankeny_lattice_q1 n q b hn_pos hq_pos
    exact hsub (by simpa [L] using hpL)

  rcases hp_ank with ⟨x, y, z, hx0, hx1, hx2, hxy, hybz⟩

  have hxyz_ne : (x, y, z) ≠ (0, 0, 0) := by
    intro hxyz
    have hx' : x = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.1) hxyz
    have hy' : y = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) hxyz
    have hz' : z = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hxyz
    have hpz : (p : E3) = 0 := by
      funext i
      fin_cases i
      · simpa [hx0, hx']
      · simpa [hx1, hy']
      · simpa [hx2, hz']
    have : p = 0 := by
      ext i
      simpa [hpz]
    exact hp0 this

  -- (a) Divisibility of `Q₁` by `n*q`.
  have hQmod : ankeny_Q1 n q x y z ≡ 0 [ZMOD (n : ℤ) * (q : ℤ)] := by
    exact ankeny_Q1_mod (n := n) (q := q) (b := b) (x := x) (y := y) (z := z)
      hnq hq_mod hxy hybz hb
  have hmul_nat : (n : ℤ) * (q : ℤ) = (n * q : ℤ) := by ring
  have hdivQ : (n * q : ℤ) ∣ ankeny_Q1 n q x y z := by
    have : (n : ℤ) * (q : ℤ) ∣ ankeny_Q1 n q x y z := (Int.modEq_zero_iff_dvd).1 hQmod
    simpa [hmul_nat] using this

  -- (b) Strict upper bound from ellipsoid membership: first bound `Q = 2q x² + y² + n z²`,
  -- then use `Q₁ ≤ Q`.
  have hp_diag_mem :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3)
        ∈ l2Ball (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) := by
    simpa [ell, ankenyEllipsoidL2_q1] using hp_mem

  have hr_nonneg :
      0 ≤ ankenyBallRadius_q1 (n : ℝ) (q : ℝ) := by
    simpa [ankenyBallRadius_q1] using Real.sqrt_nonneg (2 * ((n : ℝ) * (q : ℝ)))

  have hsum_sq_lt :
      (∑ i : Fin 3,
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
        < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
    have hp_ball :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ Metric.ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) := by
      simpa [l2Ball] using hp_diag_mem
    have :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ {w : E3L2 |
                ∑ i : Fin 3, (w i) ^ 2
                  < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2} := by
      simpa [EuclideanSpace.ball_zero_eq (n := Fin 3)
              (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) hr_nonneg]
        using hp_ball
    simpa [WithLp.ofLp_toLp] using this

  have h0 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0
        = Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have h1 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1 = ((p : E3) 1) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have h2 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2
        = Real.sqrt (n : ℝ) * ((p : E3) 2) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

  have hQ_lt_real :
      (ankeny_Q n q x y z : ℝ) < 2 * (n : ℝ) * (q : ℝ) := by
    have hsum3 :
        (Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0)) ^ 2
          + ((p : E3) 1) ^ 2
          + (Real.sqrt (n : ℝ) * ((p : E3) 2)) ^ 2
          < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
      have : (∑ i : Fin 3, (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
            =
          (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2) ^ 2 := by
        simpa [Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      have hsum3' :
          (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2) ^ 2
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [this] using hsum_sq_lt
      simpa [h0, h1, h2] using hsum3'

    have hnq_nonneg : 0 ≤ 2 * ((n : ℝ) * (q : ℝ)) := by nlinarith [le_of_lt hnR, le_of_lt hqR]
    have hr2 : (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 = 2 * (n : ℝ) * (q : ℝ) := by
      simpa [ankenyBallRadius_q1, pow_two, Real.sq_sqrt hnq_nonneg, mul_assoc, mul_left_comm, mul_comm]

    have hq_nonneg : 0 ≤ (q : ℝ) := by nlinarith
    have hx_term :
        (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
          = (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hz_term :
        (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2 = (n : ℝ) * (((z : ℤ) : ℝ) ^ 2) := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

    have : (ankeny_Q n q x y z : ℝ) < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
      have hsum3_xyz :
          (Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx0, hx1, hx2] using hsum3
      have hsqrt2q :
          Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ) =
            Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ) := by
        have : Real.sqrt (2 * (q : ℝ)) = Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) := by
          simpa using (Real.sqrt_mul (x := (2 : ℝ)) (y := (q : ℝ)) (zero_le_two : (0 : ℝ) ≤ (2 : ℝ)) hq_nonneg)
        simpa [this, mul_assoc, mul_left_comm, mul_comm]
      have hsum3_xyz' :
          (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hsqrt2q, add_assoc, add_left_comm, add_comm] using hsum3_xyz
      have :
          (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) + ((y : ℤ) : ℝ) ^ 2 + (n : ℝ) * (((z : ℤ) : ℝ) ^ 2)
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx_term, hz_term, add_assoc, add_left_comm, add_comm] using hsum3_xyz'
      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this

    simpa [hr2] using this

  have hQ1_lt_real : (ankeny_Q1 n q x y z : ℝ) < 2 * (n : ℝ) * (q : ℝ) := by
    have hx_sq_nonneg : 0 ≤ (((x : ℤ) : ℝ) ^ 2) := sq_nonneg _
    have hle_x : (q : ℝ) * (((x : ℤ) : ℝ) ^ 2) ≤ (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) := by
      have : (q : ℝ) ≤ 2 * (q : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hx_sq_nonneg
    -- Work in a normalized real-expression form to keep automation cheap.
    set xr : ℝ := ((x : ℤ) : ℝ)
    set yr : ℝ := ((y : ℤ) : ℝ)
    set zr : ℝ := ((z : ℤ) : ℝ)
    have hle :
        (q : ℝ) * (xr ^ 2) + (yr ^ 2) + (n : ℝ) * (zr ^ 2)
          ≤ (2 * (q : ℝ)) * (xr ^ 2) + (yr ^ 2) + (n : ℝ) * (zr ^ 2) := by
      nlinarith [hle_x]
    have hle' : (ankeny_Q1 n q x y z : ℝ) ≤ (ankeny_Q n q x y z : ℝ) := by
      -- unfold both sides into the same expression and apply `hle`
      simpa [ankeny_Q1, ankeny_Q, xr, yr, zr, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        using hle
    exact lt_of_le_of_lt hle' hQ_lt_real

  have hQ1_lt : ankeny_Q1 n q x y z < (2 * n * q : ℤ) := by
    exact_mod_cast hQ1_lt_real

  have hQ1_pos : 0 < ankeny_Q1 n q x y z := by
    have hQ1_nonneg : 0 ≤ ankeny_Q1 n q x y z := by
      dsimp [ankeny_Q1]
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hQ1_ne0 : ankeny_Q1 n q x y z ≠ 0 := by
      intro h0
      have hn' : (0 : ℤ) < n := by exact_mod_cast hn_pos
      have hq' : (0 : ℤ) < q := by exact_mod_cast hq_pos
      have hq_ne0 : (q : ℤ) ≠ 0 := ne_of_gt hq'
      have hn_ne0 : (n : ℤ) ≠ 0 := ne_of_gt hn'
      have hx_sq : x ^ 2 = 0 := by
        have : (q : ℤ) * x ^ 2 = 0 := by
          dsimp [ankeny_Q1] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left hq_ne0
      have hy_sq : y ^ 2 = 0 := by
        dsimp [ankeny_Q1] at h0
        nlinarith
      have hz_sq : z ^ 2 = 0 := by
        have : (n : ℤ) * z ^ 2 = 0 := by
          dsimp [ankeny_Q1] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left hn_ne0
      have hx0' : x = 0 := sq_eq_zero_iff.mp hx_sq
      have hy0' : y = 0 := sq_eq_zero_iff.mp hy_sq
      have hz0' : z = 0 := sq_eq_zero_iff.mp hz_sq
      exact hxyz_ne (by simpa [hx0', hy0', hz0'])
    exact lt_of_le_of_ne' hQ1_nonneg hQ1_ne0

  -- `Q₁` is a positive multiple of `n*q`, but also `< 2*(n*q)`, hence `Q₁ = n*q`.
  have hQ1_eq : ankeny_Q1 n q x y z = (n * q : ℤ) := by
    rcases hdivQ with ⟨t, ht⟩
    have hm_pos : 0 < (n * q : ℤ) := by
      have hnq_pos_nat : 0 < n * q := Nat.mul_pos hn_pos hq_pos
      exact_mod_cast hnq_pos_nat
    have ht_pos : 0 < t := by
      have : 0 < (n * q : ℤ) * t := by simpa [ht] using hQ1_pos
      exact pos_of_mul_pos_right this (le_of_lt hm_pos)
    have ht_lt2 : t < 2 := by
      have hbound : ankeny_Q1 n q x y z < (n * q : ℤ) * 2 := by
        have : (2 * n * q : ℤ) = (n * q : ℤ) * 2 := by ring
        simpa [this] using hQ1_lt
      have hmul : (n * q : ℤ) * t < (n * q : ℤ) * 2 := by simpa [ht] using hbound
      exact lt_of_mul_lt_mul_left hmul hm_pos.le
    have ht_eq1 : t = 1 := by omega
    -- fold `t = 1` into the divisibility witness
    have ht' : ankeny_Q1 n q x y z = (n * q : ℤ) * 1 := by
      simpa [ht_eq1] using ht
    simpa [mul_one] using ht'

  refine ⟨x, y, z, ?_, hxyz_ne, ?_, ?_⟩
  · simpa using hQ1_eq
  · simpa using hxy
  · simpa using hybz

/-- Base `p`-divisibility step used in the Ankeny reduction.

If `p ≡ 3 (mod 4)` is a prime dividing `K = n - x^2` (and `p ∤ n`), then reducing the identity
\[
  y^2 + n z^2 = 2 q K
\]
modulo `p` forces `p ∣ y` and `p ∣ z`.

This is the mod-`p` “no nontrivial \(A^2 = -B^2\)” step via
`ZMod.mod_four_ne_three_of_sq_eq_neg_sq'`.
-/
