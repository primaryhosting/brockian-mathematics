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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem prime_pow_of_introspective_aux
    (n r p B : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K] (x : K)
    (hxord : orderOf x = r)
    (hn : 2 ≤ n) (hB : n < 2 ^ B) (hr2 : 2 ≤ r) (hcopn : Nat.Coprime n r)
    (hpn : p ∣ n) (hrp : r < p)
    (hord : ∀ i, 1 ≤ i → i ≤ 100 * B ^ 2 → (n : ZMod r) ^ i ≠ 1)
    (hintro : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * B →
        Introspective r n ((X + C ((a : ℕ) : ZMod n)) : (ZMod n)[X])) :
    ∃ k, n = p ^ k := by
  classical
  by_contra hnk
  push_neg at hnk
  haveI : NeZero r := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have hcopp : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpn hcopn
  -- The multiplicative data modulo `r`.
  set u : (ZMod r)ˣ := ZMod.unitOfCoprime n hcopn with hu
  set v : (ZMod r)ˣ := ZMod.unitOfCoprime p hcopp with hv
  set Mf : Finset (ZMod r)ˣ :=
    Finset.image (fun q : Fin r × Fin r => u ^ (q.1 : ℕ) * v ^ (q.2 : ℕ)) Finset.univ with hMfdef
  set t : ℕ := Mf.card with htdef
  have hcardunits : Fintype.card (ZMod r)ˣ < r := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_lt r (by omega)
  have horder_lt : ∀ w : (ZMod r)ˣ, orderOf w < r := by
    intro w
    exact lt_of_le_of_lt (orderOf_le_card_univ) hcardunits
  have hmem : ∀ i j : ℕ, u ^ i * v ^ j ∈ Mf := by
    intro i j
    have hi : u ^ i = u ^ (i % orderOf u) := (pow_mod_orderOf u i).symm
    have hj : v ^ j = v ^ (j % orderOf v) := (pow_mod_orderOf v j).symm
    rw [hi, hj, hMfdef]
    refine Finset.mem_image.2 ⟨(⟨i % orderOf u, ?_⟩, ⟨j % orderOf v, ?_⟩), Finset.mem_univ _, rfl⟩
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos u)) (le_of_lt (horder_lt u))
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos v)) (le_of_lt (horder_lt v))
  have hMfspec : ∀ w ∈ Mf, ∃ i j : ℕ, w = u ^ i * v ^ j := by
    intro w hw
    rw [hMfdef] at hw
    obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hw
    exact ⟨q.1, q.2, hq.symm⟩
  have htr : t < r := by
    calc t ≤ Fintype.card (ZMod r)ˣ := Finset.card_le_univ Mf
      _ < r := hcardunits
  have hordu : 100 * B ^ 2 < orderOf u := by
    by_contra hcon
    push_neg at hcon
    have h1 : 1 ≤ orderOf u := orderOf_pos u
    have := pow_orderOf_eq_one u
    have h2 : ((n : ZMod r)) ^ orderOf u = 1 := by
      have h3 : ((u ^ orderOf u : (ZMod r)ˣ) : ZMod r) = 1 := by rw [this]; simp
      rw [Units.val_pow_eq_pow_val] at h3
      rw [hu] at h3
      simpa using h3
    exact hord (orderOf u) h1 hcon h2
  have htlarge : 100 * B ^ 2 < t := by
    have hsub : Finset.image (fun i : Fin (orderOf u) => u ^ (i : ℕ)) Finset.univ ⊆ Mf := by
      intro w hw
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hw
      rw [← hi]
      have := hmem (i : ℕ) 0
      simpa using this
    have hcardim : (Finset.image (fun i : Fin (orderOf u) => u ^ (i : ℕ))
        Finset.univ).card = orderOf u := by
      rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
      intro a b hab
      have := pow_injOn_Iio_orderOf (x := u) (Set.mem_Iio.2 a.isLt) (Set.mem_Iio.2 b.isLt) hab
      exact Fin.ext this
    have : orderOf u ≤ t := by
      rw [htdef, ← hcardim]
      exact Finset.card_le_card hsub
    omega
  -- Numeric consequences.
  set s := Nat.sqrt t with hsdef
  set d := 2 * (s + 1) * B with hddef
  have hdt : d < t := d_lt_t htlarge
  have h2dr : 2 * d ≤ r := two_d_le htlarge (le_of_lt htr)
  have hnpow : n ^ (2 * s) < 2 ^ d := pow_lt_two_pow_d hn hB htlarge
  have h2dl : 2 * d ≤ 4 * (Nat.sqrt r + 1) * B := by
    have : s ≤ Nat.sqrt r := Nat.sqrt_le_sqrt (le_of_lt htr)
    have : 4 * (s + 1) * B ≤ 4 * (Nat.sqrt r + 1) * B := by
      apply Nat.mul_le_mul_right
      omega
    calc 2 * d = 4 * (s + 1) * B := by rw [hddef]; ring
      _ ≤ 4 * (Nat.sqrt r + 1) * B := this
  -- Introspection over `ZMod p`.
  have hintro_p : ∀ a : ℕ, a ≤ 4 * (Nat.sqrt r + 1) * B →
      Introspective r n ((X + C ((a : ℕ) : ZMod p)) : (ZMod p)[X]) := by
    intro a ha
    have h := (hintro a ha).map (ZMod.castHom hpn (ZMod p))
    simpa using h
  have hintro_all : ∀ (T : Finset ℕ), T ⊆ Finset.range (2 * d) → ∀ i j : ℕ,
      Introspective r (n ^ i * p ^ j) (linProd p T) := by
    intro T hT i j
    refine Introspective.prod T ?_
    intro a haT
    have haltd : a < 2 * d := Finset.mem_range.1 (hT haT)
    have hbase : Introspective r n ((X + C ((a : ℕ) : ZMod p)) : (ZMod p)[X]) :=
      hintro_p a (by omega)
    exact (hbase.pow_exp i).mul_exp ((introspective_char p r _).pow_exp j)
  -- The set of evaluation points.
  have hxr : x ^ r = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  set Rt : Finset K :=
    Finset.image (fun w : (ZMod r)ˣ => x ^ ((w : ZMod r)).val) Mf with hRtdef
  have hRtcard : Rt.card = t := by
    rw [hRtdef, htdef]
    refine Finset.card_image_of_injOn ?_
    intro a _ b _ hab
    have hlt : ∀ w : (ZMod r)ˣ, ((w : ZMod r)).val < r := fun w => ZMod.val_lt _
    have := pow_injOn_Iio_orderOf (x := x)
      (Set.mem_Iio.2 (by rw [hxord]; exact hlt a)) (Set.mem_Iio.2 (by rw [hxord]; exact hlt b)) hab
    exact Units.ext (ZMod.val_injective _ this)
  -- Evaluating at powers of `x`.
  have hxpow : ∀ i j : ℕ, x ^ (n ^ i * p ^ j) = x ^ (((u ^ i * v ^ j : (ZMod r)ˣ) : ZMod r)).val := by
    intro i j
    have hcast : ((u ^ i * v ^ j : (ZMod r)ˣ) : ZMod r) = ((n ^ i * p ^ j : ℕ) : ZMod r) := by
      push_cast
      simp [hu, hv, ZMod.coe_unitOfCoprime]
    rw [hcast, ZMod.val_natCast, ← hxord, pow_mod_orderOf]
  have heval : ∀ (T : Finset ℕ), T ⊆ Finset.range (2 * d) → ∀ i j : ℕ,
      (aeval x (linProd p T)) ^ (n ^ i * p ^ j) =
        aeval (x ^ (((u ^ i * v ^ j : (ZMod r)ˣ) : ZMod r)).val) (linProd p T) := by
    intro T hT i j
    rw [← hxpow i j]
    exact aeval_pow_of_introspective hxr (hintro_all T hT i j)
  -- Injectivity of `T ↦ f_T(x)` on subsets of size `d`.
  have hinj : ∀ T ∈ Finset.powersetCard d (Finset.range (2 * d)),
      ∀ T' ∈ Finset.powersetCard d (Finset.range (2 * d)),
      aeval x (linProd p T) = aeval x (linProd p T') → T = T' := by
    intro T hT T' hT' hval
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.1 hT
    obtain ⟨hT'sub, hT'card⟩ := Finset.mem_powersetCard.1 hT'
    -- the two polynomials agree at all `t` points of `Rt`
    have hpolyeq : linProd p T = linProd p T' := by
      by_contra hne
      set g : K[X] := (linProd p T - linProd p T').map (algebraMap (ZMod p) K) with hg
      have hg0 : g ≠ 0 := by
        rw [hg]
        simp only [ne_eq, Polynomial.map_eq_zero_iff (algebraMap (ZMod p) K).injective,
          sub_eq_zero]
        exact hne
      have hdeg : g.natDegree ≤ d := by
        rw [hg]
        refine le_trans (Polynomial.natDegree_map_le) ?_
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [linProd_natDegree, linProd_natDegree, hTcard, hT'card]
        simp
      have hroots : Rt.val ⊆ g.roots := by
        intro y hy
        have hy' : y ∈ Rt := hy
        rw [hRtdef] at hy'
        obtain ⟨w, hw, hwy⟩ := Finset.mem_image.1 hy'
        obtain ⟨i, j, hij⟩ := hMfspec w hw
        rw [Polynomial.mem_roots hg0]
        rw [hg]
        simp only [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
          map_sub]
        rw [← hwy, hij, ← heval T hTsub i j, ← heval T' hT'sub i j, hval, sub_self]
      have := Polynomial.card_le_degree_of_subset_roots hroots
      rw [hRtcard] at this
      omega
    exact linProd_injOn p (2 * d) (by omega) T hTsub T' hT'sub hpolyeq
  set Img : Finset K :=
    (Finset.powersetCard d (Finset.range (2 * d))).image (fun T => aeval x (linProd p T))
    with hImgdef
  have hImgcard : Img.card = (2 * d).choose d := by
    rw [hImgdef, Finset.card_image_of_injOn (fun T hT T' hT' h => hinj T hT T' hT' h),
      Finset.card_powersetCard, Finset.card_range]
  -- Pigeonhole: two of the exponents `n^i p^j` agree modulo `r`.
  have hcardlt : Mf.card < (Finset.univ : Finset (Fin (s + 1) × Fin (s + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    have h1 : t < (Nat.sqrt t + 1) ^ 2 := Nat.lt_succ_sqrt' t
    have h2 : (s + 1) ^ 2 = (s + 1) * (s + 1) := by ring
    rw [← hsdef, h2] at h1
    omega
  obtain ⟨q₁, -, q₂, -, hq12, hqeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt
      (f := fun q : Fin (s + 1) × Fin (s + 1) => u ^ (q.1 : ℕ) * v ^ (q.2 : ℕ))
      (fun q _ => hmem _ _)
  -- The two exponents are distinct as natural numbers.
  have hne : n ^ (q₁.1 : ℕ) * p ^ (q₁.2 : ℕ) ≠ n ^ (q₂.1 : ℕ) * p ^ (q₂.2 : ℕ) := by
    intro hcon
    obtain ⟨h1, h2⟩ := nat_pow_mul_pow_injective hn hp hnk hcon
    exact hq12 (Prod.ext (Fin.ext h1) (Fin.ext h2))
  -- Every element of `Img` is a root of `X^{m₁} - X^{m₂}`.
  have hmain : ∀ m₁ m₂ : ℕ, m₂ < m₁ → m₁ ≤ n ^ (2 * s) →
      (∀ y ∈ Img, y ^ m₁ = y ^ m₂) → False := by
    intro m₁ m₂ hlt hle hy
    set g : K[X] := X ^ m₁ - X ^ m₂ with hg
    have hg0 : g ≠ 0 := by
      intro h0
      have : g.coeff m₁ = 1 := by
        rw [hg]
        simp [Polynomial.coeff_X_pow, Nat.ne_of_gt hlt]
      rw [h0] at this
      simp at this
    have hdeg : g.natDegree ≤ m₁ := by
      rw [hg]
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp
      omega
    have hsub : Img.val ⊆ g.roots := by
      intro y hy'
      rw [Polynomial.mem_roots hg0]
      simp only [hg, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [hy y hy', sub_self]
    have hcard := Polynomial.card_le_degree_of_subset_roots hsub
    rw [hImgcard] at hcard
    have h1 : 2 ^ d ≤ (2 * d).choose d := two_pow_le_choose d
    omega
  -- Apply it to the two exponents produced by the pigeonhole principle.
  have hyall : ∀ (m₁ m₂ : ℕ) (i₁ j₁ i₂ j₂ : ℕ), m₁ = n ^ i₁ * p ^ j₁ → m₂ = n ^ i₂ * p ^ j₂ →
      u ^ i₁ * v ^ j₁ = u ^ i₂ * v ^ j₂ → ∀ y ∈ Img, y ^ m₁ = y ^ m₂ := by
    intro m₁ m₂ i₁ j₁ i₂ j₂ hm₁ hm₂ hunits y hy
    rw [hImgdef] at hy
    obtain ⟨T, hT, hTy⟩ := Finset.mem_image.1 hy
    obtain ⟨hTsub, -⟩ := Finset.mem_powersetCard.1 hT
    rw [← hTy, hm₁, hm₂, heval T hTsub i₁ j₁, heval T hTsub i₂ j₂, hunits]
  have hbound : ∀ i j : ℕ, i ≤ s → j ≤ s → n ^ i * p ^ j ≤ n ^ (2 * s) := by
    intro i j hi hj
    calc n ^ i * p ^ j ≤ n ^ s * n ^ s := by
          refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hi) ?_
          calc p ^ j ≤ n ^ j := Nat.pow_le_pow_left (Nat.le_of_dvd (by omega) hpn) j
            _ ≤ n ^ s := Nat.pow_le_pow_right (by omega) hj
      _ = n ^ (2 * s) := by rw [← pow_add, two_mul]
  rcases lt_trichotomy (n ^ (q₁.1 : ℕ) * p ^ (q₁.2 : ℕ)) (n ^ (q₂.1 : ℕ) * p ^ (q₂.2 : ℕ)) with
    h | h | h
  · exact hmain _ _ h (hbound _ _ (by omega) (by omega))
      (hyall _ _ _ _ _ _ rfl rfl hqeq.symm)
  · exact hne h
  · exact hmain _ _ h (hbound _ _ (by omega) (by omega))
      (hyall _ _ _ _ _ _ rfl rfl hqeq)

/-- **The AKS criterion.** If `n ≥ 2` has a prime factor `p > r`, `n` is coprime to `r`, the
multiplicative order of `n` modulo `r` exceeds `100 B²` (where `n < 2 ^ B`), and `n` is
introspective for all the linear polynomials `X + a` with `a ≤ 4(⌊√r⌋+1)B`, then `n` is a power
of `p`. -/
