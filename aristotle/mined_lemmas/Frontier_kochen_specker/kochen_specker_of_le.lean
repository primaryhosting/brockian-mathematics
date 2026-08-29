import Mathlib

/-!
# The rays of a three dimensional Kochen–Specker configuration

The 33 rays of a Kochen–Specker configuration in `ℝ³` (coordinates in `{0, ±1, ±√2}`),
together with the auxiliary vectors completing each orthogonal pair to a frame, and the
boolean bookkeeping lemmas used in the case analysis.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
namespace KS3

/-- The three dimensional real Hilbert space. -/
abbrev V3 := EuclideanSpace ℝ (Fin 3)


theorem kochen_specker_of_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hbase : ¬ ∃ g : EuclideanSpace ℝ (Fin m) → Bool,
        ∀ v : Fin m → EuclideanSpace ℝ (Fin m),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if g (v i) then (1 : ℕ) else 0) = 1) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → Bool,
        ∀ v : Fin n → EuclideanSpace ℝ (Fin n),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rintro ⟨f, hf⟩
  have hsingle_ne : ∀ j : Fin n, (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
    intro j h
    have := congrFun (congrArg WithLp.ofLp h) j
    simp at this
  -- In the standard frame exactly one vector is assigned `1`; call its index `k`.
  have hstd := hf (fun j => EuclideanSpace.single j (1 : ℝ)) (fun j => hsingle_ne j)
    (by
      intro i j hij
      simp [EuclideanSpace.inner_single_right, EuclideanSpace.single_apply, hij.symm])
  rw [Finset.sum_boole] at hstd
  obtain ⟨k, hkS⟩ := Finset.card_eq_one.mp (by exact_mod_cast hstd)
  have hk' : ∀ j : Fin n, j ≠ k → f (EuclideanSpace.single j (1 : ℝ)) = false := by
    intro j hj
    by_contra hcon
    have hjt : f (EuclideanSpace.single j (1 : ℝ)) = true := by
      cases h : f (EuclideanSpace.single j (1 : ℝ)) <;> simp_all
    have hmem : j ∈ Finset.univ.filter
        (fun j : Fin n => f (EuclideanSpace.single j (1 : ℝ)) = true) := by simp [hjt]
    rw [hkS] at hmem
    exact hj (by simpa using hmem)
  obtain ⟨σ, hσ, hσ0⟩ := KS.exists_injection_apply_zero hm hmn k
  -- Transport the valuation to the `m`-dimensional subspace spanned by the `e (σ i)`.
  refine hbase ⟨fun x => f (KS.embed σ x), ?_⟩
  intro v hv hvo
  set V : Fin n → EuclideanSpace ℝ (Fin n) := fun j =>
    if h : j ∈ Set.range σ then KS.embed σ (v (Function.invFun σ j))
    else EuclideanSpace.single j (1 : ℝ) with hV
  have hinv : ∀ i, Function.invFun σ (σ i) = i := Function.leftInverse_invFun hσ
  have hVσ : ∀ i, V (σ i) = KS.embed σ (v i) := by
    intro i
    simp only [hV, dif_pos (Set.mem_range_self i), hinv]
  have hVnot : ∀ j, j ∉ Set.range σ → V j = EuclideanSpace.single j (1 : ℝ) := by
    intro j hj; simp only [hV, dif_neg hj]
  have hVne : ∀ j, V j ≠ 0 := by
    intro j
    by_cases h : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := h
      rw [hVσ i]
      exact KS.embed_ne_zero σ hσ (hv i)
    · rw [hVnot j h]
      exact hsingle_ne j
  have hVo : ∀ j j', j ≠ j' → inner ℝ (V j) (V j') = (0 : ℝ) := by
    intro j j' hjj'
    by_cases h : j ∈ Set.range σ <;> by_cases h' : j' ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := h
      obtain ⟨i', rfl⟩ := h'
      rw [hVσ i, hVσ i', KS.embed_inner σ hσ]
      exact hvo i i' (fun hc => hjj' (by rw [hc]))
    · obtain ⟨i, rfl⟩ := h
      rw [hVσ i, hVnot j' h', EuclideanSpace.inner_single_right]
      simp [KS.embed_apply_of_notMem σ (v i) j' h']
    · obtain ⟨i', rfl⟩ := h'
      rw [hVσ i', hVnot j h, EuclideanSpace.inner_single_left]
      simp [KS.embed_apply_of_notMem σ (v i') j h]
    · rw [hVnot j h, hVnot j' h', EuclideanSpace.inner_single_right,
        EuclideanSpace.single_apply]
      simp [hjj'.symm]
  have key := hf V hVne hVo
  rw [show (∑ j, if f (V j) then (1 : ℕ) else 0)
      = ∑ j ∈ Finset.univ.image σ, (if f (V j) then (1 : ℕ) else 0) from ?_] at key
  · rw [Finset.sum_image (fun a _ b _ h => hσ h)] at key
    simpa [hVσ] using key
  · refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    have hj' : j ∉ Set.range σ := by
      rintro ⟨i, hi⟩
      exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    have hjk : j ≠ k := by
      rintro rfl
      exact hj' ⟨⟨0, hm⟩, hσ0⟩
    rw [hVnot j hj', hk' j hjk]
    simp

/--
**Kochen–Specker theorem.**

For every dimension `n ≥ 3` there is no noncontextual hidden-variable assignment for quantum
mechanics in dimension `n`: no `{0,1}`-valued function `f` on the vectors of the `n`-dimensional
real Hilbert space assigns the value `1` to exactly one vector of each orthogonal frame
(`n` pairwise orthogonal nonzero vectors).

The three dimensional case `Frontier.kochen_specker_dim_three` is proved from an explicit
33-ray configuration, and the general case follows by restricting a hypothetical valuation to a
three dimensional coordinate subspace.
-/
