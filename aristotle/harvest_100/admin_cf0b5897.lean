/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/
noncomputable def zta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zta_prim (n : ℕ) [NeZero n] : IsPrimitiveRoot (zta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zta_pow_n (n : ℕ) [NeZero n] : (zta n) ^ n = 1 := (zta_prim n).pow_eq_one

lemma zta_pow_mod (n : ℕ) [NeZero n] (a : ℕ) : (zta n) ^ (a % n) = (zta n) ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, zta_pow_n, one_pow, one_mul]

/-! ## The characters of `ZMod n` -/

/-- The `k`-th additive character of `ZMod n`, `x ↦ ζ^(k x)`. -/
noncomputable def zchar (n : ℕ) [NeZero n] (k : ZMod n) : AddChar (ZMod n) ℂ :=
  AddChar.zmodChar n (ζ := zta n ^ k.val)
    (by rw [← pow_mul, mul_comm, pow_mul, zta_pow_n, one_pow])

lemma zchar_apply (n : ℕ) [NeZero n] (k x : ZMod n) :
    zchar n k x = (zta n) ^ (k.val * x.val) := by
  rw [zchar, AddChar.zmodChar_apply, ← pow_mul]

lemma zchar_apply' (n : ℕ) [NeZero n] (k x : ZMod n) :
    zchar n k x = (zta n) ^ (k * x).val := by
  rw [zchar_apply, ZMod.val_mul, zta_pow_mod]

lemma zchar_injective (n : ℕ) [NeZero n] : Function.Injective (zchar n) := by
  rcases eq_or_ne n 1 with rfl | hn
  · intro a b _; exact Subsingleton.elim a b
  · have hn2 : 1 < n := by have := Nat.pos_of_ne_zero (NeZero.ne n); omega
    intro a b hab
    have h1 : (1 : ZMod n).val = 1 := ZMod.val_one_eq_one_mod n ▸ Nat.mod_eq_of_lt hn2
    have h2 := congrArg (fun ψ => ψ (1 : ZMod n)) hab
    simp only [zchar_apply, h1, mul_one] at h2
    exact ZMod.val_injective n (((zta_prim n).pow_inj (ZMod.val_lt a) (ZMod.val_lt b)) h2)

/-! ## The isotypic vectors -/

/-- The `k`-th isotypic vector in the vertex space of the `n`-gon. -/
noncomputable def evec (n : ℕ) [NeZero n] (k : ZMod n) : ZMod n → ℂ := fun x => zchar n k x

lemma evec_apply (n : ℕ) [NeZero n] (k x : ZMod n) :
    evec n k x = (zta n) ^ (k * x).val := zchar_apply' n k x

lemma evec_ne_zero (n : ℕ) [NeZero n] (k : ZMod n) : evec n k ≠ 0 := by
  intro h
  have h0 : evec n k 0 = 0 := by rw [h]; rfl
  rw [evec_apply] at h0
  simp only [mul_zero, ZMod.val_zero, pow_zero] at h0
  exact one_ne_zero h0

lemma evec_injective (n : ℕ) [NeZero n] : Function.Injective (evec n) := by
  intro a b hab
  exact zchar_injective n (DFunLike.coe_injective hab)

lemma evec_neg_arg (n : ℕ) [NeZero n] (k x : ZMod n) : evec n (-k) x = evec n k (-x) := by
  simp [evec_apply, neg_mul, mul_neg]

lemma evec_add_arg (n : ℕ) [NeZero n] (k x y : ZMod n) :
    evec n k (x + y) = evec n k x * evec n k y := by
  simpa [evec] using (zchar n k).map_add_eq_mul x y

lemma evec_sub_arg (n : ℕ) [NeZero n] (k x y : ZMod n) :
    evec n k (x - y) = evec n k x * evec n (-k) y := by
  rw [sub_eq_add_neg, evec_add_arg, evec_neg_arg]

/-- Pointwise multiplication of isotypic vectors adds the isotypic labels. -/
lemma evec_mul (n : ℕ) [NeZero n] (j k : ZMod n) :
    evec n j * evec n k = evec n (j + k) := by
  funext x
  simp only [Pi.mul_apply, evec_apply, ← pow_add, add_mul]
  rw [ZMod.val_add, zta_pow_mod]

/-! ## The vertex representation of the dihedral group -/

/-- The action of the dihedral group on functions on the vertices of the `n`-gon. -/
def ngonAct (n : ℕ) (g : DihedralGroup n) (f : ZMod n → ℂ) : ZMod n → ℂ :=
  match g with
  | r i => fun x => f (x + i)
  | sr i => fun x => f (i - x)

/-- The action of a dihedral group element as a linear map. -/
def ngonLin (n : ℕ) (g : DihedralGroup n) : (ZMod n → ℂ) →ₗ[ℂ] (ZMod n → ℂ) where
  toFun := ngonAct n g
  map_add' _ _ := by cases g <;> rfl
  map_smul' _ _ := by cases g <;> rfl

/-- The vertex representation of the dihedral group `D_n` on `ZMod n → ℂ`. -/
def ngonRep (n : ℕ) : Representation ℂ (DihedralGroup n) (ZMod n → ℂ) where
  toFun := ngonLin n
  map_one' := by
    ext f x
    show ngonAct n (DihedralGroup.r 0) f x = f x
    simp [ngonAct]
  map_mul' g h := by
    ext f x
    cases g with
    | r i => cases h with
      | r j => show f _ = f _; ring_nf
      | sr j => rw [DihedralGroup.r_mul_sr]; show f _ = f _; ring_nf
    | sr i => cases h with
      | r j => rw [DihedralGroup.sr_mul_r]; show f _ = f _; ring_nf
      | sr j => rw [DihedralGroup.sr_mul_sr]; show f _ = f _; ring_nf

@[simp] lemma ngonRep_r (n : ℕ) (i : ZMod n) (f : ZMod n → ℂ) (x : ZMod n) :
    ngonRep n (r i) f x = f (x + i) := rfl

@[simp] lemma ngonRep_sr (n : ℕ) (i : ZMod n) (f : ZMod n → ℂ) (x : ZMod n) :
    ngonRep n (sr i) f x = f (i - x) := rfl

/-- Rotations act on isotypic vectors by a scalar. -/
lemma ngonRep_r_evec (n : ℕ) [NeZero n] (i k : ZMod n) :
    ngonRep n (r i) (evec n k) = (evec n k i) • evec n k := by
  funext x
  rw [ngonRep_r, evec_add_arg, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Reflections send the `k`-th isotypic vector to a multiple of the `(-k)`-th one. -/
lemma ngonRep_sr_evec (n : ℕ) [NeZero n] (i k : ZMod n) :
    ngonRep n (sr i) (evec n k) = (evec n k i) • evec n (-k) := by
  funext x
  rw [ngonRep_sr, evec_sub_arg, Pi.smul_apply, smul_eq_mul]

/-! ## The isotypic planes -/

/-- The `k`-th isotypic plane: the span of the `k`-th and `(-k)`-th isotypic vectors. -/
noncomputable def isoPlane (n : ℕ) [NeZero n] (k : ZMod n) : Submodule ℂ (ZMod n → ℂ) :=
  Submodule.span ℂ {evec n k, evec n (-k)}

lemma isoPlane_neg (n : ℕ) [NeZero n] (k : ZMod n) : isoPlane n (-k) = isoPlane n k := by
  rw [isoPlane, isoPlane, neg_neg, Set.pair_comm]

lemma evec_mem_isoPlane (n : ℕ) [NeZero n] (k : ZMod n) : evec n k ∈ isoPlane n k :=
  Submodule.subset_span (by simp)

lemma evec_neg_mem_isoPlane (n : ℕ) [NeZero n] (k : ZMod n) : evec n (-k) ∈ isoPlane n k :=
  Submodule.subset_span (by simp)

/-- Each isotypic plane is invariant under the dihedral group. -/
lemma isoPlane_map_le (n : ℕ) [NeZero n] (k : ZMod n) (g : DihedralGroup n) :
    Submodule.map (ngonRep n g) (isoPlane n k) ≤ isoPlane n k := by
  rw [isoPlane, Submodule.map_span_le]
  rintro v hv
  rcases hv with rfl | rfl
  · cases g with
    | r i => rw [ngonRep_r_evec]; exact Submodule.smul_mem _ _ (evec_mem_isoPlane n k)
    | sr i => rw [ngonRep_sr_evec]; exact Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n k)
  · cases g with
    | r i => rw [ngonRep_r_evec]; exact Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n k)
    | sr i =>
      rw [ngonRep_sr_evec, neg_neg]
      exact Submodule.smul_mem _ _ (evec_mem_isoPlane n k)

/-- Each isotypic plane is a subrepresentation. -/
theorem isoPlane_invariant (n : ℕ) [NeZero n] (k : ZMod n) (g : DihedralGroup n) :
    Submodule.map (ngonRep n g) (isoPlane n k) = isoPlane n k := by
  refine le_antisymm (isoPlane_map_le n k g) ?_
  intro v hv
  refine ⟨ngonRep n g⁻¹ v, isoPlane_map_le n k g⁻¹ ⟨v, hv, rfl⟩, ?_⟩
  have : (ngonRep n g) ((ngonRep n g⁻¹) v) = (ngonRep n (g * g⁻¹)) v := by
    rw [map_mul]; rfl
  rw [this, mul_inv_cancel, map_one]
  rfl

/-! ## Linear independence and the isotypic decomposition -/

lemma evec_linearIndependent (n : ℕ) [NeZero n] : LinearIndependent ℂ (evec n) :=
  (AddChar.linearIndependent (ZMod n) ℂ).comp (zchar n) (zchar_injective n)

/-- The isotypic vectors span the whole vertex space. -/
theorem span_range_evec (n : ℕ) [NeZero n] :
    Submodule.span ℂ (Set.range (evec n)) = ⊤ :=
  (evec_linearIndependent n).span_eq_top_of_card_eq_finrank
    (by rw [Module.finrank_fintype_fun_eq_card])

/-- The isotypic planes exhaust the vertex space. -/
theorem iSup_isoPlane (n : ℕ) [NeZero n] : (⨆ k : ZMod n, isoPlane n k) = ⊤ := by
  rw [eq_top_iff, ← span_range_evec n, Submodule.span_le]
  rintro v ⟨k, rfl⟩
  exact Submodule.mem_iSup_of_mem k (evec_mem_isoPlane n k)

/-- Isotypic planes with `k ≠ -k` are genuinely two-dimensional. -/
theorem finrank_isoPlane_of_ne (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ -k) :
    Module.finrank ℂ (isoPlane n k) = 2 := by
  have hne : evec n k ≠ evec n (-k) := fun h => hk (evec_injective n h)
  have hli : LinearIndepOn ℂ id ({evec n k, evec n (-k)} : Set (ZMod n → ℂ)) := by
    refine ((evec_linearIndependent n).linearIndepOn_id).mono ?_
    rintro v hv
    rcases hv with rfl | rfl
    · exact ⟨k, rfl⟩
    · exact ⟨-k, rfl⟩
  have := finrank_span_set_eq_card (R := ℂ) hli
  rw [isoPlane, this]
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- Isotypic planes with `k = -k` (the trivial and, for even `n`, the sign line) are lines. -/
theorem finrank_isoPlane_of_eq (n : ℕ) [NeZero n] (k : ZMod n) (hk : k = -k) :
    Module.finrank ℂ (isoPlane n k) = 1 := by
  have : ({evec n k, evec n (-k)} : Set (ZMod n → ℂ)) = {evec n k} := by
    rw [← hk]; simp
  rw [isoPlane, this]
  exact finrank_span_singleton (evec_ne_zero n k)

/-! ## Irreducibility of the isotypic planes -/

lemma evec_zero_arg (n : ℕ) [NeZero n] (k : ZMod n) : evec n k 0 = 1 := by
  rw [evec_apply]; simp

/-- If `k ≠ -k` the two isotypic vectors have different rotation eigenvalues somewhere. -/
lemma exists_evec_ne (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ -k) :
    ∃ i : ZMod n, evec n k i ≠ evec n (-k) i := by
  by_contra h
  push_neg at h
  exact hk (evec_injective n (funext h))

/-- The isotypic planes are irreducible subrepresentations: every invariant subspace of
`isoPlane n k` is either trivial or all of it. -/
theorem isoPlane_irreducible (n : ℕ) [NeZero n] (k : ZMod n)
    (W : Submodule ℂ (ZMod n → ℂ)) (hW : W ≤ isoPlane n k)
    (hinv : ∀ g : DihedralGroup n, Submodule.map (ngonRep n g) W ≤ W) :
    W = ⊥ ∨ W = isoPlane n k := by
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hW ?_)
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 h
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hW hwW)
  -- it suffices to show that `evec n k ∈ W`
  have key : evec n k ∈ W → isoPlane n k ≤ W := by
    intro hk
    have hk' : evec n (-k) ∈ W := by
      have := hinv (sr 0) ⟨evec n k, hk, rfl⟩
      rwa [ngonRep_sr_evec, evec_zero_arg, one_smul] at this
    rw [isoPlane, Submodule.span_le]
    rintro v (rfl | rfl)
    · exact hk
    · exact hk'
  rcases eq_or_ne k (-k) with hkk | hkk
  · -- degenerate case: the plane is a line
    apply key
    have hkk' : evec n (-k) = evec n k := by rw [← hkk]
    have hw : ((a + b) • evec n k : ZMod n → ℂ) = w := by
      rw [add_smul, ← hab, hkk']
    have hab0 : a + b ≠ 0 := by
      intro h0
      apply hw0
      rw [← hw, h0, zero_smul]
    have : (a + b)⁻¹ • w ∈ W := Submodule.smul_mem _ _ hwW
    rwa [← hw, smul_smul, inv_mul_cancel₀ hab0, one_smul] at this
  · -- generic case: separate the two rotation eigenlines
    obtain ⟨i, hi⟩ := exists_evec_ne n k hkk
    have hrot : (evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)) ∈ W := by
      have hmem := hinv (r i) ⟨w, hwW, rfl⟩
      have : (ngonRep n (r i)) w
          = (evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)) := by
        rw [← hab, map_add, LinearMap.map_smul, LinearMap.map_smul, ngonRep_r_evec,
          ngonRep_r_evec, smul_comm, smul_comm (b : ℂ)]
      rwa [this] at hmem
    -- subtract `evec n (-k) i • w` to isolate the `evec n k` component
    have h1 : ((evec n k i - evec n (-k) i) * a) • evec n k ∈ W := by
      have hsub : ((evec n k i - evec n (-k) i) * a) • evec n k
          = ((evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)))
            - (evec n (-k) i) • w := by
        rw [← hab]
        simp only [smul_add, smul_smul]
        rw [sub_mul]
        module
      rw [hsub]
      exact Submodule.sub_mem _ hrot (Submodule.smul_mem _ _ hwW)
    have h2 : ((evec n (-k) i - evec n k i) * b) • evec n (-k) ∈ W := by
      have hsub : ((evec n (-k) i - evec n k i) * b) • evec n (-k)
          = ((evec n k i) • (a • evec n k) + (evec n (-k) i) • (b • evec n (-k)))
            - (evec n k i) • w := by
        rw [← hab]
        simp only [smul_add, smul_smul]
        rw [sub_mul]
        module
      rw [hsub]
      exact Submodule.sub_mem _ hrot (Submodule.smul_mem _ _ hwW)
    have hd : evec n k i - evec n (-k) i ≠ 0 := sub_ne_zero.2 hi
    have hd' : evec n (-k) i - evec n k i ≠ 0 := sub_ne_zero.2 (Ne.symm hi)
    rcases eq_or_ne a 0 with rfl | ha
    · -- then `b ≠ 0`, so `evec n (-k) ∈ W`, hence `evec n k ∈ W`
      have hb : b ≠ 0 := by
        intro rfl
        exact hw0 (by rw [← hab]; simp)
      have hmem : evec n (-k) ∈ W := by
        have hc : ((evec n (-k) i - evec n k i) * b) ≠ 0 := mul_ne_zero hd' hb
        have := Submodule.smul_mem W (((evec n (-k) i - evec n k i) * b)⁻¹) h2
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      apply key
      have := hinv (sr 0) ⟨evec n (-k), hmem, rfl⟩
      rwa [ngonRep_sr_evec, evec_zero_arg, one_smul, neg_neg] at this
    · apply key
      have hc : ((evec n k i - evec n (-k) i) * a) ≠ 0 := mul_ne_zero hd ha
      have := Submodule.smul_mem W (((evec n k i - evec n (-k) i) * a)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-! ## The fusion rule: pentagon ⊗ pentagon -/

/-- The pointwise product of vectors from the `j`-th and `k`-th isotypic planes lies in
the sum of the `(j+k)`-th and `(j-k)`-th isotypic planes. -/
theorem isoPlane_mul_isoPlane (n : ℕ) [NeZero n] (j k : ZMod n)
    {u v : ZMod n → ℂ} (hu : u ∈ isoPlane n j) (hv : v ∈ isoPlane n k) :
    u * v ∈ isoPlane n (j + k) ⊔ isoPlane n (j - k) := by
  rw [isoPlane, Submodule.mem_span_pair] at hu hv
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  have key : (a • evec n j + b • evec n (-j)) * (c • evec n k + d • evec n (-k))
      = ((a * c) • evec n (j + k) + (b * d) • evec n (-(j + k)))
        + ((a * d) • evec n (j - k) + (b * c) • evec n (-(j - k))) := by
    have h1 : evec n j * evec n k = evec n (j + k) := evec_mul n j k
    have h2 : evec n (-j) * evec n (-k) = evec n (-(j + k)) := by
      rw [evec_mul]; ring_nf
    have h3 : evec n j * evec n (-k) = evec n (j - k) := by
      rw [evec_mul]; ring_nf
    have h4 : evec n (-j) * evec n k = evec n (-(j - k)) := by
      rw [evec_mul]; ring_nf
    rw [add_mul, mul_add, mul_add]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
      h1, h2, h3, h4]
    abel
  rw [key]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.mem_sup_left (Submodule.add_mem _
      (Submodule.smul_mem _ _ (evec_mem_isoPlane n (j + k)))
      (Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n (j + k))))
  · exact Submodule.mem_sup_right (Submodule.add_mem _
      (Submodule.smul_mem _ _ (evec_mem_isoPlane n (j - k)))
      (Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n (j - k))))

/-! ## The main theorem -/

/-- **Pentagon Pentagon Isotypic, higher `n`.**

For every `n ≥ 1`, the vertex space `ZMod n → ℂ` of the regular `n`-gon, carrying the
natural representation of the dihedral group `D_n` (rotations `r i : f ↦ f(· + i)` and
reflections `sr i : f ↦ f(i - ·)`), decomposes into isotypic planes
`isoPlane n k = span {e_k, e_{-k}}`, where `e_k x = ζ^(k x)` for a primitive `n`-th root of
unity `ζ`:

1. each isotypic plane is a subrepresentation (invariant under all of `D_n`);
2. the isotypic planes exhaust the vertex space;
3. the plane `isoPlane n k` is two-dimensional exactly in the generic case `k ≠ -k`, and is
   a line in the degenerate cases `k = -k` (i.e. `k = 0`, and `k = n/2` for even `n`);
4. each isotypic plane is irreducible: its only invariant subspaces are `⊥` and itself;
5. the "pentagon ⊗ pentagon" fusion rule: the pointwise product of vectors of the `j`-th and
   `k`-th isotypic planes lies in `isoPlane n (j+k) ⊔ isoPlane n (j-k)`.

For `n = 5` this is the classical decomposition of the pentagon representation of `D₅`. -/
theorem PentagonPentagonIsotypicHigherN (n : ℕ) [NeZero n] :
    (∀ (k : ZMod n) (g : DihedralGroup n),
        Submodule.map (ngonRep n g) (isoPlane n k) = isoPlane n k)
    ∧ (⨆ k : ZMod n, isoPlane n k) = ⊤
    ∧ (∀ k : ZMod n, k ≠ -k → Module.finrank ℂ (isoPlane n k) = 2)
    ∧ (∀ k : ZMod n, k = -k → Module.finrank ℂ (isoPlane n k) = 1)
    ∧ (∀ (k : ZMod n) (W : Submodule ℂ (ZMod n → ℂ)), W ≤ isoPlane n k →
        (∀ g : DihedralGroup n, Submodule.map (ngonRep n g) W ≤ W) →
        W = ⊥ ∨ W = isoPlane n k)
    ∧ (∀ (j k : ZMod n) (u v : ZMod n → ℂ), u ∈ isoPlane n j → v ∈ isoPlane n k →
        u * v ∈ isoPlane n (j + k) ⊔ isoPlane n (j - k)) :=
  ⟨isoPlane_invariant n, iSup_isoPlane n, finrank_isoPlane_of_ne n, finrank_isoPlane_of_eq n,
    isoPlane_irreducible n,
    fun j k _ _ hu hv => isoPlane_mul_isoPlane n j k hu hv⟩

/-- The pentagon case `n = 5`: the vertex space of the pentagon splits as the trivial line
`isoPlane 5 0` together with the two two-dimensional isotypic planes `isoPlane 5 1` and
`isoPlane 5 2`. -/
theorem PentagonIsotypicDecomposition :
    isoPlane 5 0 ⊔ isoPlane 5 1 ⊔ isoPlane 5 2 = ⊤
    ∧ Module.finrank ℂ (isoPlane 5 0) = 1
    ∧ Module.finrank ℂ (isoPlane 5 1) = 2
    ∧ Module.finrank ℂ (isoPlane 5 2) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← iSup_isoPlane 5, iSup_le_iff]
    intro k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = -(2 : ZMod 5) ∨ k = -(1 : ZMod 5) := by
      revert k; decide
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
    · rw [isoPlane_neg]; exact le_sup_right
    · rw [isoPlane_neg]; exact le_sup_of_le_left le_sup_right
  · exact finrank_isoPlane_of_eq 5 0 (by decide)
  · exact finrank_isoPlane_of_ne 5 1 (by decide)
  · exact finrank_isoPlane_of_ne 5 2 (by decide)

end

end Brockian

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

