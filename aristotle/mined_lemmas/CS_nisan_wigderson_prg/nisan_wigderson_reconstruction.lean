import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/

theorem nisan_wigderson_reconstruction {n l m α : ℕ} (hm : 0 < m)
    (S : Fin m → Fin l → Fin n) (hinj : ∀ i, Function.Injective (S i))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (S i)) ∩ (Finset.univ.image (S j))).card ≤ α)
    (f : (Fin l → Bool) → Bool) (D : (Fin m → Bool) → Bool) (ε : ℝ)
    (hdist : ε < (∑ x : Fin n → Bool, bv (D (nwGen S f x))) / 2 ^ n
              - (∑ z : Fin m → Bool, bv (D z)) / 2 ^ m) :
    ∃ (g : Fin m → (Fin l → Bool) → Bool) (c : Bool),
      (∀ j, IsJunta α (g j)) ∧
      (1 : ℝ) / 2 + ε / m
        ≤ ((Finset.univ.filter
            (fun y : Fin l → Bool => xor (D (fun j => g j y)) c = f y)).card : ℝ) / 2 ^ l := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hL : (0 : ℝ) < 2 ^ l := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- the endpoints of the hybrid sequence
  have hPm : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f m x r))
      = 2 ^ m * ∑ x : Fin n → Bool, bv (D (nwGen S f x)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h : ∀ r : Fin m → Bool, hyb S f m x r = nwGen S f x := by
      intro r; funext j; simp [hyb, nwGen, j.isLt]
    simp [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP0 : ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f 0 x r))
      = 2 ^ n * ∑ z : Fin m → Bool, bv (D z) := by
    have h : ∀ (x r : _), hyb S f 0 x (r : Fin m → Bool) = r := by
      intro x r; funext j; simp [hyb]
    simp [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the hybrid argument
  obtain ⟨k, hk, hgap⟩ :=
    exists_hybrid_gap hm (fun k => ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, bv (D (hyb S f k x r)))
      (ε * (2 ^ n * 2 ^ m)) (by
        simp only [hPm, hP0]
        have h1 : (2 ^ n * 2 ^ m : ℝ) * ε
            < (2 ^ n * 2 ^ m : ℝ) * ((∑ x : Fin n → Bool, bv (D (nwGen S f x))) / 2 ^ n
                - (∑ z : Fin m → Bool, bv (D z)) / 2 ^ m) :=
          mul_lt_mul_of_pos_left hdist (by positivity)
        have h2 : (2 ^ n * 2 ^ m : ℝ) * ((∑ x : Fin n → Bool, bv (D (nwGen S f x))) / 2 ^ n
                - (∑ z : Fin m → Bool, bv (D z)) / 2 ^ m)
            = 2 ^ m * (∑ x : Fin n → Bool, bv (D (nwGen S f x)))
              - 2 ^ n * ∑ z : Fin m → Bool, bv (D z) := by
          field_simp
        rw [h2] at h1
        linarith)
  set i : Fin m := ⟨k, hk⟩ with hidef
  have hik : (i : ℕ) = k := rfl
  -- Yao's next-bit predictor
  have hyao := yao_sum S f D k i hik
  have hbig : (2 : ℝ) ^ n * 2 ^ m * (1 / 2 + ε / m)
      < ∑ x : Fin n → Bool, ∑ r : Fin m → Bool, succTerm S f D k i x r := by
    rw [hyao]
    have : (2 : ℝ) ^ n * 2 ^ m * (1 / 2 + ε / m)
        = 2 ^ n * 2 ^ m / 2 + ε * (2 ^ n * 2 ^ m) / m := by ring
    rw [this]
    linarith
  -- fix the seed outside the `i`-th index set, and the random bits
  have hov : ∀ r : Fin m → Bool,
      ∑ x : Fin n → Bool, ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x y) r
        = 2 ^ l * ∑ x : Fin n → Bool, succTerm S f D k i x r :=
    fun r => sum_ov (hinj i) (fun x => succTerm S f D k i x r)
  have hconst : ∑ _r : Fin m → Bool, ∑ _x : Fin n → Bool, ((2 : ℝ) ^ l * (1 / 2 + ε / m))
      = 2 ^ n * 2 ^ m * (2 ^ l * (1 / 2 + ε / m)) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have htot : ∑ _r : Fin m → Bool, ∑ _x : Fin n → Bool, ((2 : ℝ) ^ l * (1 / 2 + ε / m))
      < ∑ r : Fin m → Bool, ∑ x : Fin n → Bool,
          ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x y) r := by
    rw [hconst]
    have h1 : ∑ r : Fin m → Bool, ∑ x : Fin n → Bool,
        ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x y) r
        = 2 ^ l * ∑ r : Fin m → Bool, ∑ x : Fin n → Bool, succTerm S f D k i x r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => hov r
    rw [h1, Finset.sum_comm,
      show (2 : ℝ) ^ n * 2 ^ m * (2 ^ l * (1 / 2 + ε / m))
        = 2 ^ l * (2 ^ n * 2 ^ m * (1 / 2 + ε / m)) from by ring]
    exact mul_lt_mul_of_pos_left hbig hL
  obtain ⟨r₀, -, h1⟩ := Finset.exists_lt_of_sum_lt htot
  obtain ⟨x₀, -, h2⟩ := Finset.exists_lt_of_sum_lt h1
  -- the reconstructed predictor
  refine ⟨fun j y => if (j : ℕ) < k then f (fun t => ov (S i) x₀ y (S j t)) else r₀ j,
    !(r₀ i), ?_, ?_⟩
  · -- each coordinate function is an `α`-junta
    intro j
    by_cases hj : (j : ℕ) < k
    · refine ⟨Finset.univ.filter (fun v : Fin l => ∃ u, S j u = S i v), ?_, ?_⟩
      · have hmaps : ∀ v ∈ Finset.univ.filter (fun v : Fin l => ∃ u, S j u = S i v),
            S i v ∈ (Finset.univ.image (S i)) ∩ (Finset.univ.image (S j)) := by
          intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨u, hu⟩ := hv.2
          exact Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨v, Finset.mem_univ v, rfl⟩,
            Finset.mem_image.2 ⟨u, Finset.mem_univ u, hu⟩⟩
        refine le_trans (Finset.card_le_card_of_injOn (S i)
          (fun v hv => Finset.mem_coe.2 (hmaps v (Finset.mem_coe.1 hv)))
          (fun a _ b _ h => hinj i h)) (hdesign i j ?_)
        intro h
        have hji : (j : ℕ) = k := by rw [← h]; exact hik
        omega
      · intro y y' hyy
        simp only [if_pos hj]
        congr 1
        funext t
        by_cases hv : ∃ v, S i v = S j t
        · obtain ⟨v, hv'⟩ := hv
          rw [← hv', ov_apply (hinj i), ov_apply (hinj i)]
          exact hyy v (Finset.mem_filter.2 ⟨Finset.mem_univ v, ⟨t, hv'.symm⟩⟩)
        · simp only [ov, dif_neg hv]
    · exact ⟨∅, by simp, fun y y' _ => by simp only [if_neg hj]⟩
  · -- the predictor agrees with `f` often
    have hcount : ∑ y : Fin l → Bool, succTerm S f D k i (ov (S i) x₀ y) r₀
        = ((Finset.univ.filter (fun y : Fin l → Bool =>
            xor (D (fun j => if (j : ℕ) < k then f (fun t => ov (S i) x₀ y (S j t)) else r₀ j))
              (!(r₀ i)) = f y)).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun y _ => ?_
      have e1 : hyb S f k (ov (S i) x₀ y) r₀
          = fun j => if (j : ℕ) < k then f (fun t => ov (S i) x₀ y (S j t)) else r₀ j := by
        funext j
        rfl
      have e2 : f (fun t => ov (S i) x₀ y (S i t)) = f y := by
        congr 1
        funext t
        exact ov_apply (hinj i) _ _ t
      simp only [succTerm, e1, e2]
    rw [hcount] at h2
    rw [le_div_iff₀ hL]
    linarith [h2]

end NW

end CS

