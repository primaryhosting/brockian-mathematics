import RequestProject.Huffman

/-!
# Achievability of the Huffman cost

Companion to `RequestProject.Huffman`.  Here we show that the Huffman cost is *attained*:
there really is a prefix code whose expected codeword length equals `CS.huffCost`.

Combined with the optimality bound `CS.huffman_optimal`, this gives
`CS.huffman_isLeast`: the Huffman cost is the least expected codeword length among all
prefix codes.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-- A multiset of binary codewords is prefix-free: the codewords are pairwise distinct and
none is a prefix of another. -/

theorem kraft_finset_le : ∀ n : ℕ, ∀ C : Finset (List Bool), (∀ l ∈ C, l.length ≤ n) →
    PrefixFreeSet C → ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro C hlen _
      have hsub : C ⊆ {([] : List Bool)} := by
        intro l hl
        have := hlen l hl
        simp only [Finset.mem_singleton]
        exact List.length_eq_zero_iff.1 (by omega)
      calc ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length
          ≤ ∑ l ∈ ({([] : List Bool)} : Finset (List Bool)), ((2:ℝ)⁻¹) ^ l.length := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro i _ _; positivity
        _ = 1 := by simp
  | succ n ih =>
      intro C hlen hpf
      by_cases hnil : ([] : List Bool) ∈ C
      · have hsub : C ⊆ {([] : List Bool)} := by
          intro l hl
          simp only [Finset.mem_singleton]
          by_contra hne
          exact hpf [] hnil l hl (Ne.symm hne) List.nil_prefix
        calc ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length
            ≤ ∑ l ∈ ({([] : List Bool)} : Finset (List Bool)), ((2:ℝ)⁻¹) ^ l.length := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
              intro i _ _; positivity
          _ = 1 := by simp
      · -- every codeword is nonempty, so split according to the first bit
        have key : ∀ b : Bool,
            ∑ l ∈ C.filter (fun l => l.head? = some b), ((2:ℝ)⁻¹) ^ l.length ≤ (2:ℝ)⁻¹ := by
          intro b
          set D := C.filter (fun l => l.head? = some b) with hD
          set Cb := D.image List.tail with hCb
          have hDmem : ∀ l ∈ D, l = b :: l.tail := by
            intro l hl
            rw [hD, Finset.mem_filter] at hl
            cases l with
            | nil => simp at hl
            | cons c t => simp at hl ⊢; exact hl.2
          have hDeq : D = Cb.image (List.cons b) := by
            ext l
            constructor
            · intro hl
              rw [Finset.mem_image]
              exact ⟨l.tail, by rw [hCb, Finset.mem_image]; exact ⟨l, hl, rfl⟩, (hDmem l hl).symm⟩
            · intro hl
              rw [Finset.mem_image] at hl
              obtain ⟨t, ht, rfl⟩ := hl
              rw [hCb, Finset.mem_image] at ht
              obtain ⟨m, hm, rfl⟩ := ht
              rw [← hDmem m hm]; exact hm
          have hsum : ∑ l ∈ D, ((2:ℝ)⁻¹) ^ l.length
              = (2:ℝ)⁻¹ * ∑ t ∈ Cb, ((2:ℝ)⁻¹) ^ t.length := by
            rw [hDeq, Finset.sum_image (by intro x _ y _ h; exact List.cons_injective h),
              Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro t _
            simp [pow_succ]
            ring
          have hlenb : ∀ t ∈ Cb, t.length ≤ n := by
            intro t ht
            rw [hCb, Finset.mem_image] at ht
            obtain ⟨m, hm, rfl⟩ := ht
            have hmC : m ∈ C := by rw [hD, Finset.mem_filter] at hm; exact hm.1
            have h3 := hlen m hmC
            rw [hDmem m hm] at h3
            simpa using h3
          have hpfb : PrefixFreeSet Cb := by
            intro t ht t' ht' hne hpre
            have hmem : ∀ s ∈ Cb, b :: s ∈ C := by
              intro s hs
              have : b :: s ∈ D := by rw [hDeq, Finset.mem_image]; exact ⟨s, hs, rfl⟩
              rw [hD, Finset.mem_filter] at this; exact this.1
            exact hpf (b :: t) (hmem t ht) (b :: t') (hmem t' ht')
              (by simpa using hne) (by simpa using hpre)
          have hih := ih Cb hlenb hpfb
          rw [hsum]
          nlinarith [hih]
        have hsplit : ∑ l ∈ C, ((2:ℝ)⁻¹) ^ l.length
            = ∑ l ∈ C.filter (fun l => l.head? = some false), ((2:ℝ)⁻¹) ^ l.length
              + ∑ l ∈ C.filter (fun l => l.head? = some true), ((2:ℝ)⁻¹) ^ l.length := by
          rw [← Finset.sum_filter_add_sum_filter_not C (fun l => l.head? = some false)]
          congr 1
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext l
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hl, h2⟩
            refine ⟨hl, ?_⟩
            cases l with
            | nil => exact absurd hl hnil
            | cons c t => cases c <;> simp_all
          · rintro ⟨hl, h2⟩
            refine ⟨hl, ?_⟩
            cases l with
            | nil => exact absurd hl hnil
            | cons c t => cases c <;> simp_all
        rw [hsplit]
        have h1 := key false
        have h2 := key true
        linarith

/-! ## Prefix codes -/

/-- `c` is a prefix code: the codewords of distinct symbols are never prefixes of one
another. -/
