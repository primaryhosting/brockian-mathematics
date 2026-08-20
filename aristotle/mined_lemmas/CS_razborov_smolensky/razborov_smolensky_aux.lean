import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

theorem razborov_smolensky_aux {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (F : Type) [Field F] [CharP F q] (ζ : F) (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) :
    ¬ InAC0mod q (MODfun p) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  rintro ⟨d0, c0, H⟩
  obtain ⟨t, l, m, hl, -, hparam1, hparam2⟩ :=
    exists_params p q (d0 + 1) (c0 + 1) hp.two_le (by omega) (by omega)
  set D := ((q - 1) * l) ^ (d0 + 1) with hD
  have hbase : 1 ≤ (q - 1) * l :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := hq.two_le; omega) (by omega))
  -- the circuit computing `MOD p` on `(2 * m + 1) + p` inputs
  obtain ⟨k, C, o, hk, hdepth, heval⟩ := H (2 * m + 1 + p)
  have hk1 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) o.2
  -- Razborov's approximation
  obtain ⟨P, B, hB, hPdeg, hPcorr⟩ := approx_circuit (q := q) (n := 2 * m + 1 + p) l hl C
  have hPo : P o ∈ Deg (ZMod q) (2 * m + 1 + p) D := by
    refine mem_Deg_of_le (hPdeg o) ?_
    exact Nat.pow_le_pow_right hbase (le_trans hdepth (by omega))
  set φ : ZMod q →+* F := ZMod.castHom (dvd_refl q) F with hφ
  -- the shifted inputs
  set e : Fin p → Cube p := fun j => fun i => decide ((i : ℕ) < (p - (j : ℕ)) % p) with he
  set g : Fin p → Cube (2 * m + 1) → Cube (2 * m + 1 + p) :=
    fun j x => Fin.append x (e j) with hg
  set Q : Fin p → Cube (2 * m + 1) → F := fun j x => φ (P o (g j x)) with hQ
  set Bad : Fin p → Finset (Cube (2 * m + 1)) :=
    fun j => Finset.univ.filter (fun x => g j x ∈ B) with hBad
  set G : Finset (Cube (2 * m + 1)) := Finset.univ \ (Finset.univ.biUnion Bad) with hG
  -- the degrees
  have hQdeg : ∀ j : Fin p, Q j ∈ Deg F (2 * m + 1) D := by
    intro j
    have h1 : (fun z => φ (P o z)) ∈ Deg F (2 * m + 1 + p) D := map_mem_Deg φ hPo
    refine comp_mem_Deg (g j) ?_ h1
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro a
      have h2 : (fun x : Cube (2 * m + 1) => coord F (Fin.castAdd p a) (g j x)) = coord F a := by
        funext x
        simp [hg, coord, Fin.append_left]
      rw [h2]
      exact coord_mem_Deg a le_rfl
    · intro b
      have h2 : (fun x : Cube (2 * m + 1) => coord F (Fin.natAdd (2 * m + 1) b) (g j x))
          = fun _ => coord F b (e j) := by
        funext x
        simp [hg, coord, Fin.append_right]
      rw [h2]
      exact const_mem_Deg _ _
  -- the values
  have honesE : ∀ j : Fin p, ones (e j) = (p - (j : ℕ)) % p := by
    intro j
    have hfilter : (Finset.univ.filter (fun i : Fin p => e j i = true))
        = Finset.filter (fun i : Fin p => (i : ℕ) < (p - (j : ℕ)) % p) Finset.univ := by
      apply Finset.filter_congr
      intro i _
      simp [he]
    rw [ones, hfilter]
    exact card_filter_val_lt p _ (le_of_lt (Nat.mod_lt _ hp.pos))
  have hQcorr : ∀ j : Fin p, ∀ x ∈ G, Q j x = if ones x % p = (j : ℕ) then 1 else 0 := by
    intro j x hxG
    have hxB : g j x ∉ B := by
      intro hmem
      have h1 : x ∈ Bad j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem⟩
      have h2 : x ∈ Finset.univ.biUnion Bad := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h1⟩
      exact (Finset.mem_sdiff.1 hxG).2 h2
    have h1 : P o (g j x) = bit q (C.eval q (g j x) o) := hPcorr o _ hxB
    rw [heval] at h1
    have h2 : ones (g j x) = ones x + (p - (j : ℕ)) % p := by
      rw [hg]
      simp only
      rw [ones_append, honesE j]
    have h3 : (p ∣ ones (g j x)) ↔ ones x % p = (j : ℕ) := by
      rw [h2]
      exact dvd_add_sub_mod hp.pos j.2
    have h4 : Q j x = φ (bit q (MODfun p (2 * m + 1 + p) (g j x))) := by rw [hQ]; simp only [h1]
    rw [h4, MODfun]
    by_cases hcase : ones x % p = (j : ℕ)
    · rw [if_pos hcase, decide_eq_true (h3.2 hcase)]
      simp [bit]
    · have h5 : ¬ (p ∣ ones (g j x)) := fun hdv => hcase (h3.1 hdv)
      rw [if_neg hcase, decide_eq_false h5]
      simp [bit]
  -- the size of the good set
  have hGcard : 2 ^ (2 * m + 1) ≤ G.card + p * B.card := by
    have h2 : ∀ j : Fin p, (Bad j).card ≤ B.card := by
      intro j
      refine Finset.card_le_card_of_injOn (g j) ?_ ?_
      · intro x hx
        have := (Finset.mem_filter.1 (by simpa using hx : x ∈ Bad j)).2
        simpa using this
      · intro x _ y _ hxy
        funext i
        have h3 := congrFun hxy (Fin.castAdd p i)
        simpa [hg, Fin.append_left] using h3
    have h1 : (Finset.univ.biUnion Bad).card ≤ ∑ j : Fin p, (Bad j).card :=
      Finset.card_biUnion_le
    have h3 : ∑ j : Fin p, (Bad j).card ≤ p * B.card := by
      calc ∑ j : Fin p, (Bad j).card ≤ ∑ _j : Fin p, B.card :=
            Finset.sum_le_sum (fun j _ => h2 j)
        _ = p * B.card := by simp
    have h4 : G.card + (Finset.univ.biUnion Bad).card
        = (Finset.univ : Finset (Cube (2 * m + 1))).card := by
      rw [hG]
      exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    have h5 : (Finset.univ : Finset (Cube (2 * m + 1))).card = 2 ^ (2 * m + 1) := by
      simp [Finset.card_univ]
    omega
  -- Smolensky's bound
  have hsmol : G.card ≤ ((Finset.univ : Finset (Finset (Fin (2 * m + 1)))).filter
      (fun S => S.card ≤ m + D)).card :=
    smolensky_bound hp.pos ζ hζ1 hζp le_rfl G Q hQdeg hQcorr
  have hcount : G.card ≤ 4 ^ m + D * ((2 * m + 1).choose m) := by
    refine le_trans hsmol ?_
    rw [card_filter_card_le (2 * m + 1) (m + D)]
    exact sum_choose_le m D
  -- the two quantitative estimates
  have hR1 : 8 * p * k * 2 ^ p ≤ 2 ^ l := by
    refine hparam1 k (le_trans hk ?_)
    have h1 : (2 * m + 1 + p + 1) ^ c0 ≤ (2 * m + 1 + p + 1) ^ (c0 + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.mul_le_mul (by omega) h1
  have hR2 : 9 * D ^ 2 ≤ m := hparam2
  -- `4 * (p * |B|) ≤ 4 ^ m`
  have hb : 4 * (p * B.card) ≤ 4 ^ m := by
    have h1 : B.card * (8 * p * k * 2 ^ p) ≤ B.card * 2 ^ l := Nat.mul_le_mul_left _ hR1
    have h3 : (2 : ℕ) ^ (2 * m + 1 + p) = 2 * 4 ^ m * 2 ^ p := by
      rw [pow_add, pow_succ, pow_mul]; norm_num; ring
    have h4 : B.card * (8 * p * k * 2 ^ p) ≤ k * (2 * 4 ^ m * 2 ^ p) := by
      rw [← h3]
      exact le_trans h1 hB
    have h5 : (2 * (4 * (p * B.card))) * (k * 2 ^ p) ≤ (2 * 4 ^ m) * (k * 2 ^ p) := by
      calc (2 * (4 * (p * B.card))) * (k * 2 ^ p) = B.card * (8 * p * k * 2 ^ p) := by ring
        _ ≤ k * (2 * 4 ^ m * 2 ^ p) := h4
        _ = (2 * 4 ^ m) * (k * 2 ^ p) := by ring
    have h6 : 0 < k * 2 ^ p := by positivity
    have h7 : 2 * (4 * (p * B.card)) ≤ 2 * 4 ^ m := Nat.le_of_mul_le_mul_right h5 h6
    exact Nat.le_of_mul_le_mul_left h7 (by norm_num)
  -- the final contradiction
  have hfinal : 2 * 4 ^ m ≤ G.card + p * B.card := by
    have h1 : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul]; norm_num; ring
    omega
  exact final_arith hb (choose_mul_lt hR2) (by omega)

/-- **Razborov–Smolensky.**  For distinct primes `p` and `q`, the function `MOD p` is not in
`AC⁰[q]`: it is not computed by any family of constant depth, polynomial size circuits with
unbounded fan-in `AND`, `OR`, `NOT` and `MOD q` gates. -/
