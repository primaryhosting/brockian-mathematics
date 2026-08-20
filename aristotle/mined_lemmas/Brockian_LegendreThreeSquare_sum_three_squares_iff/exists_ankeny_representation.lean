import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_ankeny_representation (n q : ℕ) (b : ℤ) (hn_pos : 0 < n) (hn_odd : Odd n) (hq : Nat.Prime q)
    (_hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    ∃ x y z : ℤ,
      2 * q * x^2 + y^2 + n * z^2 = 2 * n * q ∧
      (x, y, z) ≠ (0, 0, 0) ∧
      x ≡ y [ZMOD (n : ℤ)] ∧
      y ≡ b * z [ZMOD (2 * q : ℤ)] := by
  classical
  -- The Ankeny ellipsoid in `E3`, expressed via an L2-ball preimage.
  let ell (nR qR : ℝ) : Set E3 := ankenyEllipsoidL2 nR qR

  have hq_pos : 0 < q := hq.pos

  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos

  -- Lattice + fundamental domain: use the explicit span lattice so `Countable ↥L` is available.
  let L : AddSubgroup E3 := ankeny_span_lattice n q b hn_pos hq_pos
  let F : Set E3 := ankeny_span_fundamentalDomain n q b hn_pos hq_pos

  -- Provide the `Countable ↥L` instance required by Minkowski.
  letI : Countable (↥L) := by
    -- `L` is (definitionally) a `Submodule.span ℤ` of a finite set, hence countable.
    change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn_pos hq_pos)))
    infer_instance

  have hfund : IsAddFundamentalDomain L F volume := by
    simpa [L, F] using ankeny_span_isAddFundamentalDomain n q b hn_pos hq_pos

  have hvolF : volume F = (2 * n * q : ℝ≥0∞) := by
    simpa [F] using ankeny_span_volume_fundamentalDomain n q b hn_pos hq_pos

  -- Symmetry: `x ∈ ell → -x ∈ ell`.
  have hsymm : ∀ x ∈ ell (n : ℝ) (q : ℝ), -x ∈ ell (n : ℝ) (q : ℝ) := by
    intro x hx
    dsimp [ell, ankenyEllipsoidL2, l2Ball] at hx ⊢
    -- `toLp` and `ankenyDiagMap` commute with negation, and the ball around `0` is symmetric.
    simpa [Metric.mem_ball, map_neg, dist_eq_norm, norm_neg] using hx

  -- Convexity: preimage of a convex ball under an affine map.
  have hconv : Convex ℝ (ell (n : ℝ) (q : ℝ)) := by
    -- Use the linear-equivalence spelling of `toLp` to build an affine map.
    let toLpLin : E3 →ₗ[ℝ] E3L2 :=
      (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ E3).symm.toLinearMap
    let f : E3 →ᵃ[ℝ] E3L2 :=
      toLpLin.toAffineMap.comp (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ)).toAffineMap
    have hs :
        ell (n : ℝ) (q : ℝ) =
          f ⁻¹' Metric.ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) := by
      ext x
      rfl
    simpa [hs, ell, l2Ball, f, toLpLin] using
      (Convex.affine_preimage
        (f := f)
        (s := Metric.ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)))
        (convex_ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ))))

  -- Left side simplification: `finrank E3 = 3`.
  have hrank : Module.finrank ℝ E3 = 3 := by simp [E3]

  -- Use the explicit volume formula and a coarse lower bound.
  have hineq :
      volume F * 2 ^ (Module.finrank ℝ E3) < volume (ell (n : ℝ) (q : ℝ)) := by
    have hL : volume F * 2 ^ (Module.finrank ℝ E3) = (16 * n * q : ℝ≥0∞) := by
      simp [hvolF, hrank, pow_succ, mul_left_comm, mul_comm]
      ring
    have hR : (16 * n * q : ℝ≥0∞) < volume (ell (n : ℝ) (q : ℝ)) := by
      simpa [ell] using volume_ankenyEllipsoidL2_gt_nat (n := n) (q := q) hn_pos hq_pos
    calc
      volume F * 2 ^ (Module.finrank ℝ E3) = (16 * n * q : ℝ≥0∞) := hL
      _ < volume (ell (n : ℝ) (q : ℝ)) := hR

  rcases
      GeometryOfNumbers.minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
        (μ := volume) (L := L) (F := F) (s := ell (n : ℝ) (q : ℝ))
        hfund hsymm hconv hineq
    with ⟨p, hp0, hp_mem⟩

  -- Step 4: convert `p ∈ L` into explicit integer coordinates via the congruence-defined lattice.
  have hpL : ((p : E3) ∈ L) := p.property
  have hp_ank : (p : E3) ∈ ankeny_lattice n q b := by
    -- `L = ankeny_span_lattice ...` by definition, and we have an inclusion lemma.
    have hsub := ankeny_span_lattice_subset_ankeny_lattice n q b hn_pos hq_pos
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
      -- ext on the underlying function
      ext i
      simpa [hpz]
    exact hp0 this

  -- Step 5: the arithmetic pin-down `Q = 2*n*q` from:
  -- - divisibility `Q ≡ 0 (mod 2*n*q)` (CRT glue), and
  -- - strict bound `0 < Q < 4*n*q` (ellipsoid membership).

  -- (a) Divisibility of `Q` by `2*n*q`.
  have hQmod : ankeny_Q n q x y z ≡ 0 [ZMOD (2 * n * q : ℤ)] := by
    simpa using ankeny_Q_mod n q b x y z hn_odd hq_mod hxy hybz hb
  have hdivQ : (2 * n * q : ℤ) ∣ ankeny_Q n q x y z :=
    (Int.modEq_zero_iff_dvd).1 hQmod

  -- (b) Strict upper bound from ellipsoid membership.
  have hp_diag_mem :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3)
        ∈ l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) := by
    -- `p ∈ diagMap⁻¹' l2Ball ...`
    simpa [ell, ankenyEllipsoidL2] using hp_mem

  have hr_nonneg :
      0 ≤ GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ) := by
    -- `2 * sqrt(n*q) ≥ 0`.
    have hs : 0 ≤ Real.sqrt ((n : ℝ) * (q : ℝ)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    simpa [GeometryOfNumbers.Minkowski.ankenyBallRadius, mul_assoc] using mul_nonneg h2 hs

  have hsum_sq_lt :
      (∑ i : Fin 3,
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
        < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
    -- Unfold `l2Ball` (preimage of a Euclidean ball) and use the standard `ball_zero_eq` characterization.
    have hp_ball :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ Metric.ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) := by
      simpa [l2Ball] using hp_diag_mem
    have :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ {w : E3L2 |
                ∑ i : Fin 3, (w i) ^ 2
                  < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2} := by
      simpa [EuclideanSpace.ball_zero_eq (n := Fin 3)
              (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) hr_nonneg]
        using hp_ball
    -- `toLp` is the identity on coordinates, so we can drop it.
    simpa [WithLp.ofLp_toLp] using this

  -- Expand the diagonal map coordinatewise.
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
      (ankeny_Q n q x y z : ℝ) < 4 * (n : ℝ) * (q : ℝ) := by
    -- First rewrite the sum into three coordinates and apply `hsum_sq_lt`.
    have hsum3 :
        (Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0)) ^ 2
          + ((p : E3) 1) ^ 2
          + (Real.sqrt (n : ℝ) * ((p : E3) 2)) ^ 2
          < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
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
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        -- rewrite the sum and use the bound
        simpa [this] using hsum_sq_lt
      simpa [h0, h1, h2] using hsum3'

    -- Convert the radius square to `4*n*q` and replace `p` coordinates by `(x,y,z)`.
    have hnq_nonneg : 0 ≤ (n : ℝ) * (q : ℝ) := by nlinarith
    have hr2 : (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 = 4 * (n : ℝ) * (q : ℝ) := by
      -- Avoid `simp` here (it can open irrelevant side goals). Do it by hand.
      set s : ℝ := Real.sqrt ((n : ℝ) * (q : ℝ))
      calc
        (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2
            = (2 * s) ^ 2 := by simp [GeometryOfNumbers.Minkowski.ankenyBallRadius, s]
        _ = 4 * (s ^ 2) := by
          simp [pow_two]
          ring
        _ = 4 * ((n : ℝ) * (q : ℝ)) := by
          -- `s^2 = n*q`
          simpa [s] using congrArg (fun t : ℝ => (4 : ℝ) * t) (Real.sq_sqrt hnq_nonneg)
        _ = 4 * (n : ℝ) * (q : ℝ) := by ring

    -- Now: LHS = `Q` as a real number.
    have hn_nonneg : 0 ≤ (n : ℝ) := by nlinarith
    have hq_nonneg : 0 ≤ (q : ℝ) := by nlinarith
    have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have hx_term :
        (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
          = (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) := by
      -- `(√2 * √q * x)^2 = 2*q*x^2`
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hz_term :
        (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2 = (n : ℝ) * (((z : ℤ) : ℝ) ^ 2) := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

    -- Rewrite `hsum3` into the exact inequality on `Q`.
    have : (ankeny_Q n q x y z : ℝ) < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
      -- substitute `p 0 = x`, `p 1 = y`, `p 2 = z`
      have hsum3_xyz :
          (Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx0, hx1, hx2] using hsum3

      -- Rewrite the `x`-term into the split-sqrt form expected by our `hx_term`.
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
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hsqrt2q, add_assoc, add_left_comm, add_comm] using hsum3_xyz

      -- Turn LHS into `ankeny_Q` (as ℝ).
      have : (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) + ((y : ℤ) : ℝ) ^ 2 + (n : ℝ) * (((z : ℤ) : ℝ) ^ 2)
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx_term, hz_term, add_assoc, add_left_comm, add_comm] using hsum3_xyz'

      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
    -- replace RHS by `4*n*q`
    simpa [hr2] using this

  have hQ_lt : ankeny_Q n q x y z < (4 * n * q : ℤ) := by
    exact_mod_cast hQ_lt_real

  have hQ_pos : 0 < ankeny_Q n q x y z := by
    -- `Q = 0` would force `x=y=z=0`, contradicting `hxyz_ne`.
    have hQ_nonneg : 0 ≤ ankeny_Q n q x y z := by
      dsimp [ankeny_Q]
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hQ_ne0 : ankeny_Q n q x y z ≠ 0 := by
      intro h0
      have hn' : (0 : ℤ) < n := by exact_mod_cast hn_pos
      have h2q_ne0 : (2 * (q : ℤ)) ≠ 0 := by
        have h2q_pos_nat : 0 < 2 * q := Nat.mul_pos (by decide : 0 < (2 : ℕ)) hq_pos
        exact ne_of_gt (by exact_mod_cast h2q_pos_nat)
      have hn_ne0 : (n : ℤ) ≠ 0 := ne_of_gt hn'
      -- from `Q=0` and nonnegativity of terms, force each square to be zero
      have hx_sq : x ^ 2 = 0 := by
        have : (2 * (q : ℤ)) * x ^ 2 = 0 := by
          dsimp [ankeny_Q] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left h2q_ne0
      have hy_sq : y ^ 2 = 0 := by
        dsimp [ankeny_Q] at h0
        nlinarith
      have hz_sq : z ^ 2 = 0 := by
        have : (n : ℤ) * z ^ 2 = 0 := by
          dsimp [ankeny_Q] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left hn_ne0
      have hx0' : x = 0 := sq_eq_zero_iff.mp hx_sq
      have hy0' : y = 0 := sq_eq_zero_iff.mp hy_sq
      have hz0' : z = 0 := sq_eq_zero_iff.mp hz_sq
      exact hxyz_ne (by simpa [hx0', hy0', hz0'])
    exact lt_of_le_of_ne' hQ_nonneg hQ_ne0

  -- (d) `Q` is a positive multiple of `2*n*q`, but also `Q < 2*(2*n*q)`, hence `Q = 2*n*q`.
  have hQ_eq : ankeny_Q n q x y z = (2 * n * q : ℤ) := by
    rcases hdivQ with ⟨t, ht⟩
    have hm_pos : 0 < (2 * n * q : ℤ) := by
      have h2n : 0 < 2 * n := Nat.mul_pos (by decide : 0 < (2 : ℕ)) hn_pos
      have h2nq : 0 < (2 * n) * q := Nat.mul_pos h2n hq_pos
      -- normalize to `2*n*q`
      have : 0 < 2 * n * q := by simpa [Nat.mul_assoc] using h2nq
      exact_mod_cast this
    have ht_pos : 0 < t := by
      have : 0 < (2 * n * q : ℤ) * t := by simpa [ht] using hQ_pos
      exact pos_of_mul_pos_right this (le_of_lt hm_pos)
    have ht_lt2 : t < 2 := by
      have hbound : ankeny_Q n q x y z < (2 * n * q : ℤ) * 2 := by
        have : (4 * n * q : ℤ) = (2 * n * q : ℤ) * 2 := by ring
        simpa [this] using hQ_lt
      have hmul : (2 * n * q : ℤ) * t < (2 * n * q : ℤ) * 2 := by
        -- avoid `simp` here; a `calc` with `ht.symm` is much cheaper
        calc
          (2 * n * q : ℤ) * t = ankeny_Q n q x y z := ht.symm
          _ < (2 * n * q : ℤ) * 2 := hbound
      exact lt_of_mul_lt_mul_left hmul hm_pos.le
    have ht_eq1 : t = 1 := by omega
    -- fold `t = 1` into the divisibility witness
    have ht' : ankeny_Q n q x y z = (2 * n * q : ℤ) * 1 := by
      simpa [ht_eq1] using ht
    simpa [mul_one] using ht'

  refine ⟨x, y, z, ?_, hxyz_ne, ?_, ?_⟩
  -- Unfold `Q` back into the target equation.
  simpa [ankeny_Q] using hQ_eq
  · -- `x ≡ y [ZMOD n]` from lattice membership.
    simpa using hxy
  · -- `y ≡ b*z [ZMOD 2q]` from lattice membership.
    -- `hybz : y ≡ b*z [ZMOD 2*q]` already has the right modulus.
    simpa [mul_assoc] using hybz

set_option maxHeartbeats 1200000 in
/-- Minkowski application (Q₁ route): there exists a representation
`q x^2 + y^2 + n z^2 = n*q` under the `q ≡ -1 (mod n)` arithmetic interface. -/
