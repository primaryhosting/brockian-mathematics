import Mathlib

/-!
# The Erdős–Anning theorem

An infinite set of points in the Euclidean plane whose pairwise distances are all integers
must be collinear.

## Proof outline

Assume `S` is infinite with integral pairwise distances and pick `A ≠ B` in `S`.  If some
`C ∈ S` is off the line `AB`, then `A`, `B`, `C` form a non-degenerate triangle.  For every
`P ∈ S` the two differences `dist P A - dist P B` and `dist P A - dist P C` are integers
bounded in absolute value by `dist A B` and `dist A C` respectively, so only finitely many
pairs of values occur (`finite_of_not_collinear`).  The heart of the argument (`key`) shows
that three *distinct* points cannot share the same pair of differences: writing
`⟪P - A, B - A⟫` in terms of the distances (`inner_formula`) shows that all such points lie
on a common line `A + p + x • q` with `x = dist P A`, and `‖p + x • q‖ = x` can hold for at
most two values of `x` unless `p = 0` and `‖q‖ = 1` (`key_p_zero`), in which case `B - A`
and `C - A` are both multiples of `q`, contradicting non-collinearity.  Hence `S` would be
finite, a contradiction.
-/

namespace Brockian.MsErdosAnning

open scoped RealInnerProductSpace

/-! ### Auxiliary algebraic lemmas -/

/-- A real quadratic with three distinct roots is identically zero. -/

lemma finite_of_not_collinear {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, dist x y = n)
    {A B C : EuclideanSpace ℝ (Fin 2)} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) : S.Finite := by
  -- For each point P in S, define signature s(P) = (d1, d2) where
  -- d1 = dist P A - dist P B and d2 = dist P A - dist P C
  -- By exists_int_diff, d1 and d2 are integers.
  -- By triangle inequality: |d1| ≤ dist A B and |d2| ≤ dist A C
  -- So there are finitely many possible signatures.
  -- By key, each signature corresponds to at most 2 points.
  -- Therefore S is finite.
  
  -- First, bound the possible values of d1 and d2 using triangle inequality
  let M1 : ℤ := ⌈dist A B⌉
  let M2 : ℤ := ⌈dist A C⌉
  
  -- The signature function
  let σ : EuclideanSpace ℝ (Fin 2) → ℤ × ℤ := fun P =>
    ((⌊dist P A - dist P B⌋, ⌊dist P A - dist P C⌋))
  
  -- The signature values are bounded by the side lengths
  -- We'll show the range is a subset of a finite product of finite sets
  have hbound : ∀ P ∈ S, 
      -M1 ≤ ⌊dist P A - dist P B⌋ ∧ ⌊dist P A - dist P B⌋ ≤ M1 ∧ 
      -M2 ≤ ⌊dist P A - dist P C⌋ ∧ ⌊dist P A - dist P C⌋ ≤ M2 := by
    intro P hP
    -- Use triangle inequality: |dist P A - dist P B| ≤ dist A B
    -- Triangle inequality
    -- dist_triangle P A B : dist P B ≤ dist P A + dist A B
    have htri1 : dist P B ≤ dist P A + dist A B := dist_triangle P A B
    have htri2 : dist P A ≤ dist P B + dist A B := by simpa [dist_comm A B] using dist_triangle P B A
    have htri3 : dist P C ≤ dist P A + dist A C := dist_triangle P A C
    have htri4 : dist P A ≤ dist P C + dist A C := by simpa [dist_comm A C] using dist_triangle P C A
    -- Derive bounds on differences
    have h1 : dist P A - dist P B ≤ dist A B := by linarith
    have h2 : dist P B - dist P A ≤ dist A B := by linarith
    have h3 : dist P A - dist P C ≤ dist A C := by linarith
    have h4 : dist P C - dist P A ≤ dist A C := by linarith
    -- Now bound the floor values
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- -M1 ≤ ⌊dist P A - dist P B⌋
      have h5 : -(dist A B) ≤ dist P A - dist P B := by linarith
      have h6 : ⌊-(dist A B)⌋ ≤ ⌊dist P A - dist P B⌋ := Int.floor_mono h5
      have h7 : -⌈dist A B⌉ ≤ ⌊-(dist A B)⌋ := by simp [Int.floor_neg]
      linarith
    · -- ⌊dist P A - dist P B⌋ ≤ M1
      calc ⌊dist P A - dist P B⌋ ≤ ⌊dist A B⌋ := Int.floor_mono h1
        _ ≤ ⌈dist A B⌉ := Int.floor_le_ceil _
    · -- -M2 ≤ ⌊dist P A - dist P C⌋
      have h5 : -(dist A C) ≤ dist P A - dist P C := by linarith
      have h6 : ⌊-(dist A C)⌋ ≤ ⌊dist P A - dist P C⌋ := Int.floor_mono h5
      have h7 : -⌈dist A C⌉ ≤ ⌊-(dist A C)⌋ := by simp [Int.floor_neg]
      linarith
    · -- ⌊dist P A - dist P C⌋ ≤ M2
      calc ⌊dist P A - dist P C⌋ ≤ ⌊dist A C⌋ := Int.floor_mono h3
        _ ≤ ⌈dist A C⌉ := Int.floor_le_ceil _
  
  -- So the range of σ on S is finite
  have hrange_finite : (Set.range (σ ∘ Subtype.val : S → ℤ × ℤ)).Finite := by
    -- The range is contained in a finite product of finite sets
    let bounds : Set (ℤ × ℤ) := {p | -M1 ≤ p.1 ∧ p.1 ≤ M1 ∧ -M2 ≤ p.2 ∧ p.2 ≤ M2}
    have hbounds_finite : bounds.Finite := by
      apply Set.Finite.subset (Set.Finite.prod (Set.finite_Icc (-M1) M1) (Set.finite_Icc (-M2) M2))
      intro p hp
      rw [Set.mem_prod]
      simp at hp ⊢
      exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩
    apply Set.Finite.subset hbounds_finite
    intro p hp
    simp only [Set.mem_range] at hp
    obtain ⟨⟨P, hP⟩, hPp⟩ := hp
    rw [← hPp]
    exact hbound P hP
  
  -- Each fiber has at most 2 points by key
  -- Use Set.Finite.of_finite_image_union_preimage or similar
  -- Define the inclusion S → S (as subtype) and compose with σ
  let f : S → ℤ × ℤ := σ ∘ Subtype.val
  have hf_image_finite : (f '' Set.univ).Finite := by
    convert hrange_finite
    ext x
    simp [f]
  -- Each fiber f⁻¹({r}) has at most 2 elements
  have hfiber_card : ∀ r, (f ⁻¹' {r}).Finite := by
    intro r
    -- The fiber over r consists of elements x : S with f x = r
    -- i.e., points P ∈ S with σ P = r
    -- By key, at most 2 such points exist
    by_contra hinf
    -- Extract 3 distinct points from the infinite fiber
    have hInf : Set.Infinite (f ⁻¹' {r}) := by simpa using hinf
    -- Get 3 distinct elements
    obtain ⟨p, hp⟩ := Set.Infinite.nonempty hInf
    have hInf1 : Set.Infinite ((f ⁻¹' {r}) \ {p}) := by
      by_contra hfin
      apply hInf
      exact Set.Finite.subset (Set.Finite.union (not_not.mp hfin) (Set.finite_singleton p))
        (fun x hx => by simp at hx ⊢; tauto)
    obtain ⟨q, hq_set, hq'⟩ := Set.Infinite.nonempty hInf1
    have hInf2 : Set.Infinite ((f ⁻¹' {r}) \ ({p, q} : Set S)) := by
      by_contra hfin
      apply hInf
      exact Set.Finite.subset (Set.Finite.union (not_not.mp hfin) (Set.toFinite {p, q}))
        (fun x hx => by simp at hx ⊢; tauto)
    obtain ⟨s, hs_set, hs'⟩ := Set.Infinite.nonempty hInf2
    -- These are 3 distinct elements with f p = f q = f s = r
    have hp_eq : f p = r := hp
    have hq_eq : f q = r := hq_set
    have hs_eq : f s = r := hs_set
    -- Convert to points in EuclideanSpace
    let P := p.val
    let Q := q.val
    let R := s.val
    have hP : P ∈ S := p.property
    have hQ : Q ∈ S := q.property
    have hR : R ∈ S := s.property
    have hpq : P ≠ Q := by
      intro h
      have heq : p = q := Subtype.ext h
      exact hq' heq.symm
    have hps : P ≠ R := by
      intro h
      have heq : p = s := Subtype.ext h
      simp [heq] at hs'
    have hqs : Q ≠ R := by
      intro h
      have heq : q = s := Subtype.ext h
      simp [heq] at hs'
    -- Extract the signature values
    have hr1 : ⌊dist P A - dist P B⌋ = r.1 := by
      have := congrArg Prod.fst hp_eq
      simp [f, σ] at this
      exact this
    have hr2 : ⌊dist P A - dist P C⌋ = r.2 := by
      have := congrArg Prod.snd hp_eq
      simp [f, σ] at this
      exact this
    have hq1 : ⌊dist Q A - dist Q B⌋ = r.1 := by
      have := congrArg Prod.fst hq_eq
      simp [f, σ] at this
      exact this
    have hq2 : ⌊dist Q A - dist Q C⌋ = r.2 := by
      have := congrArg Prod.snd hq_eq
      simp [f, σ] at this
      exact this
    have hs1 : ⌊dist R A - dist R B⌋ = r.1 := by
      have := congrArg Prod.fst hs_eq
      simp [f, σ] at this
      exact this
    have hs2 : ⌊dist R A - dist R C⌋ = r.2 := by
      have := congrArg Prod.snd hs_eq
      simp [f, σ] at this
      exact this
    -- The distance differences are integers (by exists_int_diff)
    obtain ⟨d1, hd1⟩ := exists_int_diff hint hP hA hB
    obtain ⟨d2, hd2⟩ := exists_int_diff hint hP hA hC
    -- Since the floors equal r.1 and r.2, and the values are integers, we have:
    have hP_d1 : dist P A - dist P B = r.1 := by rw [hd1]; simp_all
    have hP_d2 : dist P A - dist P C = r.2 := by rw [hd2]; simp_all
    have hQ_d1 : dist Q A - dist Q B = r.1 := by
      obtain ⟨d1Q, hd1Q⟩ := exists_int_diff hint hQ hA hB
      rw [hd1Q]; simp_all
    have hQ_d2 : dist Q A - dist Q C = r.2 := by
      obtain ⟨d2Q, hd2Q⟩ := exists_int_diff hint hQ hA hC
      rw [hd2Q]; simp_all
    have hR_d1 : dist R A - dist R B = r.1 := by
      obtain ⟨d1S, hd1S⟩ := exists_int_diff hint hR hA hB
      rw [hd1S]; simp_all
    have hR_d2 : dist R A - dist R C = r.2 := by
      obtain ⟨d2S, hd2S⟩ := exists_int_diff hint hR hA hC
      rw [hd2S]; simp_all
    -- Apply key: we have P, Q, R with same distance differences
    have e1Q : dist Q A - dist Q B = dist P A - dist P B := by rw [hQ_d1, hP_d1]
    have e1S : dist R A - dist R B = dist P A - dist P B := by rw [hR_d1, hP_d1]
    have e2Q : dist Q A - dist Q C = dist P A - dist P C := by rw [hQ_d2, hP_d2]
    have e2S : dist R A - dist R C = dist P A - dist P C := by rw [hR_d2, hP_d2]
    exact key hABC hpq hps hqs e1Q e1S e2Q e2S
  -- By contradiction: if S is infinite, some fiber is infinite
  -- But each fiber has ≤ 2 points by key
  by_contra hinf
  -- The infinite set S maps to a finite set via f, so some fiber is infinite
  -- f '' Set.univ is finite, Set.univ (the subtype) is infinite
  -- By Set.Infinite.exists_infinite_fiber, some fiber is infinite
  have hfiber_infinite : ∃ r, Set.Infinite (f ⁻¹' {r}) := by
    by_contra h
    push_neg at h
    -- Every fiber is finite
    have hfib_all_finite : ∀ r, (f ⁻¹' {r}).Finite := h
    -- The union of all fibers is Set.univ
    have hunion : ⋃ r, f ⁻¹' {r} = Set.univ := by ext x; simp
    -- Set.univ is infinite (since S is infinite)
    have huniv_inf : Set.Infinite (Set.univ : Set S) := by
      by_contra hfin
      push_neg at hfin
      have hS_fin : S.Finite := by
        have : Finite S := Set.finite_univ_iff.mp hfin
        exact Set.finite_coe_iff.mpr this
      exact hinf hS_fin
    -- Infinite set cannot be union of finitely many finite sets
    have hfiber_range_fin : (Set.range f).Finite := by
      simp only [Set.range, Set.image_univ] at hf_image_finite ⊢
      exact hf_image_finite
    have hsub : (Set.univ : Set S) ⊆ ⋃ r ∈ Set.range f, f ⁻¹' {r} := fun x _ => by
      simp only [Set.mem_iUnion]
      use f x
      simp
    have hunion_fin : (⋃ r ∈ Set.range f, f ⁻¹' {r}).Finite := by
      apply Set.Finite.biUnion hfiber_range_fin
      intro r _
      exact hfib_all_finite r
    exact huniv_inf (Set.Finite.subset hunion_fin hsub)
  obtain ⟨r, hr_inf⟩ := hfiber_infinite
  -- A fiber corresponds to points with the same signature (d1, d2)
  -- By key, at most 2 such points exist
  exact hr_inf (hfiber_card r)

/-- If `x` is not on the line through the distinct points `A` and `B`, then `A`, `B`, `x` are
not collinear. -/
