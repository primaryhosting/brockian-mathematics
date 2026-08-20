import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

theorem or_approx (ℓ D : ℕ) (G : Finset (Cube n))
    (s : Finset (Fin m)) (p : Fin m → Cube n → ZMod 3) (w : Cube n → Fin m → Bool)
    (hp : ∀ j ∈ s, p j ∈ Deg n D)
    (hpw : ∀ j ∈ s, ∀ x ∈ G, p j x = bit (w x j)) :
    ∃ q : Cube n → ZMod 3, q ∈ Deg n (2 * ℓ * D) ∧ ∃ E : Finset (Cube n),
      2 ^ ℓ * E.card ≤ 2 ^ n ∧
      ∀ x ∈ G, x ∉ E → q x = bit (decide (∃ j ∈ s, w x j = true)) := by
  classical
  set Q : (Fin ℓ → Finset (Fin m)) → Cube n → ZMod 3 :=
    fun T => 1 - ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, p j) ^ 2) with hQ
  -- degree bound
  have hQdeg : ∀ T, Q T ∈ Deg n (2 * ℓ * D) := by
    intro T
    have h1 : ∀ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, p j) ^ 2 : Cube n → ZMod 3) ∈ Deg n (2 * D) := by
      intro r
      have hsum : (∑ j ∈ s ∩ T r, p j) ∈ Deg n D :=
        Submodule.sum_mem _ (fun j hj => hp j (Finset.mem_of_mem_inter_left hj))
      have hsq : ((∑ j ∈ s ∩ T r, p j) ^ 2 : Cube n → ZMod 3) ∈ Deg n (D + D) := by
        rw [sq]; exact Deg_mul hsum hsum
      have h := Submodule.sub_mem _ (one_mem_Deg (D + D)) hsq
      rwa [← two_mul] at h
    have h2 := Deg_prod (Finset.univ : Finset (Fin ℓ))
      (fun r => 1 - (∑ j ∈ s ∩ T r, p j) ^ 2) (2 * D) (fun r _ => h1 r)
    have hc : (Finset.univ : Finset (Fin ℓ)).card * (2 * D) = 2 * ℓ * D := by
      rw [Finset.card_univ, Fintype.card_fin]; ring
    rw [hc] at h2
    exact Submodule.sub_mem _ (one_mem_Deg _) h2
  -- value on `G`
  have hQval : ∀ T, ∀ x ∈ G,
      Q T x = 1 - ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, bit (w x j)) ^ 2) := by
    intro T x hx
    simp only [hQ, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply,
      Finset.sum_apply]
    congr 1
    refine Finset.prod_congr rfl (fun r _ => ?_)
    congr 2
    exact Finset.sum_congr rfl (fun j hj => hpw j (Finset.mem_of_mem_inter_left hj) x hx)
  set Bad : (Fin ℓ → Finset (Fin m)) → Finset (Cube n) := fun T =>
    G.filter (fun x => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)
    with hBad
  have hgood : ∀ T, ∀ x ∈ G, x ∉ Bad T → Q T x = bit (decide (∃ j ∈ s, w x j = true)) := by
    intro T x hxG hxB
    rw [hQval T x hxG]
    by_cases hex : ∃ j ∈ s, w x j = true
    · have hne : ∃ r, (∑ j ∈ s ∩ T r, bit (w x j)) ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hxB (Finset.mem_filter.mpr ⟨hxG, hex, hc⟩)
      obtain ⟨r, hr⟩ := hne
      have hzero : ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, bit (w x j)) ^ 2) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ r) (zmod3_one_sub_sq_of_ne_zero _ hr)
      rw [hzero, sub_zero]
      simp [hex, bit]
    · have hz : ∀ r : Fin ℓ, (∑ j ∈ s ∩ T r, bit (w x j)) = 0 := by
        intro r
        refine Finset.sum_eq_zero (fun j hj => ?_)
        have hne : w x j ≠ true := fun h => hex ⟨j, Finset.mem_of_mem_inter_left hj, h⟩
        simp only [ne_eq, Bool.not_eq_true] at hne
        simp [hne, bit]
      have hone : ∏ r : Fin ℓ, (1 - (∑ j ∈ s ∩ T r, bit (w x j)) ^ 2) = 1 :=
        Finset.prod_eq_one (fun r _ => zmod3_one_sub_sq_of_eq_zero _ (hz r))
      rw [hone, sub_self]
      simp [hex, bit]
  -- counting: some `T` has a small bad set
  have hswap : ∑ T : (Fin ℓ → Finset (Fin m)), (Bad T).card
      = ∑ x ∈ G, ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card := by
    simp only [hBad, Finset.card_filter]
    rw [Finset.sum_comm]
  have hpt : ∀ x : Cube n, 2 ^ ℓ * ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
      (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
      ≤ (2 ^ m) ^ ℓ := by
    intro x
    by_cases hex : ∃ j ∈ s, w x j = true
    · obtain ⟨j₀, hj₀s, hj₀⟩ := hex
      have hfe : ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0))
          = ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)) := by
        apply Finset.filter_congr
        intro T _
        simp only [and_iff_right_iff_imp]
        exact fun _ => ⟨j₀, hj₀s, hj₀⟩
      have hcf : ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
          = ((Finset.univ : Finset (Finset (Fin m))).filter
            (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)).card ^ ℓ :=
        card_filter_pi (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)
      rw [hfe, hcf]
      have hhalf := card_subsets_sum_zero_le s (fun j => bit (w x j)) j₀ hj₀s (by simp [hj₀])
      calc 2 ^ ℓ * ((Finset.univ : Finset (Finset (Fin m))).filter
              (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)).card ^ ℓ
          = (2 * ((Finset.univ : Finset (Finset (Fin m))).filter
              (fun U => ∑ j ∈ s ∩ U, bit (w x j) = 0)).card) ^ ℓ := by rw [mul_pow]
        _ ≤ (2 ^ m) ^ ℓ := Nat.pow_le_pow_left hhalf ℓ
    · have : ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
          (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun T _ => ?_)
        simp only [not_and]
        exact fun h => absurd h hex
      simp [this]
  have hcard : ∑ T : (Fin ℓ → Finset (Fin m)), 2 ^ ℓ * (Bad T).card
      ≤ ∑ _T : (Fin ℓ → Finset (Fin m)), 2 ^ n := by
    rw [← Finset.mul_sum, hswap, Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    have h1 : ∑ x ∈ G, 2 ^ ℓ * ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
        (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
        ≤ ∑ _x ∈ G, (2 ^ m) ^ ℓ := Finset.sum_le_sum (fun x _ => hpt x)
    have h2 : G.card ≤ 2 ^ n := by
      have := Finset.card_le_card (Finset.subset_univ G)
      simpa [Finset.card_univ, card_cube] using this
    have h3 : Fintype.card (Fin ℓ → Finset (Fin m)) = (2 ^ m) ^ ℓ := by
      simp [Fintype.card_finset]
    rw [Finset.sum_const, smul_eq_mul] at h1
    rw [h3, smul_eq_mul]
    calc ∑ x ∈ G, 2 ^ ℓ * ((Finset.univ : Finset (Fin ℓ → Finset (Fin m))).filter
        (fun T => (∃ j ∈ s, w x j = true) ∧ ∀ r, (∑ j ∈ s ∩ T r, bit (w x j)) = 0)).card
        ≤ G.card * (2 ^ m) ^ ℓ := h1
      _ ≤ 2 ^ n * (2 ^ m) ^ ℓ := Nat.mul_le_mul_right _ h2
      _ = (2 ^ m) ^ ℓ * 2 ^ n := by ring
  obtain ⟨T, -, hT⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty (α := Fin ℓ → Finset (Fin m))) hcard
  exact ⟨Q T, hQdeg T, Bad T, hT, hgood T⟩

end CS

import RequestProject.Degree

/-!
# The dimension argument

If a function of degree at most `D` agrees with the parity monomial
`mon univ` on a set `A ⊆ Cube n` (with `n = 2 * N`), then

  `|A| ≤ ∑_{k ≤ N + D} C(n, k)`.

This is the standard linear-algebraic step of Smolensky's argument: on `A`,
every monomial can be replaced by one of degree at most `N + D`, so the
`|A|`-dimensional space of all functions on `A` is spanned by that many
monomials.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The number of subsets of `Fin n` of size at most `K`. -/
