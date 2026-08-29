/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## The Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for quantum mechanics in dimension `d`
assigns, to every one-dimensional projector (equivalently, to every nonzero vector of
`ℝ^d`, or of `ℂ^d`), a definite truth value `0`/`1`, in a way that does not depend on
which measurement context the projector is being measured in.  The only constraint
imposed by quantum mechanics is that, for every orthogonal basis `b₀, …, b_{d-1}`
(i.e. every complete measurement context), *exactly one* of the corresponding
projectors gets the value `1`.

The Kochen–Specker theorem says that for `d ≥ 3` no such assignment exists.  Here we
formalize the theorem in dimension `d = 4`, which is the standard "base case" admitting
a short combinatorial proof: the 18-vector, 9-basis configuration of
Cabello–Estebaranz–García-Alcaine.  Each of the 18 vectors occurs in exactly two of the
9 orthogonal bases, so summing the "exactly one `1` per basis" constraint over the nine
bases gives `9 = 2 · (number of vectors valued 1)`, an odd number equal to an even one.

The vector space is modelled as `Fin 4 → ℝ` with the standard inner product
`⟪v, w⟫ = ∑ k, v k * w k`, and a context is any 4-tuple of pairwise orthogonal nonzero
vectors (necessarily an orthogonal basis of `ℝ⁴`).  The assignment is modelled as an
arbitrary function `f` from vectors to `Bool`; noncontextuality is expressed by the fact
that `f` depends only on the vector, not on the context in which it appears.
-/

namespace Frontier

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker
configuration in `ℝ⁴`. -/
def ksVec : Fin 18 → (Fin 4 → ℝ) :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 0], ![1, -1, 0, 0], ![0, 1, 0, 0],
    ![1, 0, 1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1], ![1, -1, -1, 1], ![0, 0, 1, 1],
    ![1, 1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0],
    ![1, 1, -1, 1], ![1, 1, 1, -1], ![-1, 1, 1, 1]]

/-- The nine orthogonal bases of the configuration, described by the indices (into
`ksVec`) of their four members.  Each of the eighteen indices occurs in exactly two
of the nine bases. -/
def ksBasis : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3], ![0, 4, 5, 6], ![7, 8, 2, 9], ![7, 10, 6, 11], ![1, 4, 12, 13],
    ![8, 10, 13, 14], ![15, 16, 3, 9], ![15, 17, 5, 11], ![16, 17, 12, 14]]

/-- Every vector occurring in the configuration is nonzero. -/
lemma ksVec_ne_zero (n : Fin 9) (i : Fin 4) : ksVec (ksBasis n i) ≠ 0 := by
  fin_cases n <;> fin_cases i <;>
    · intro h
      simp [ksVec, ksBasis, funext_iff, Fin.forall_fin_succ] at h

/-- Each of the nine listed contexts consists of pairwise orthogonal vectors. -/
lemma ksBasis_orthogonal (n : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    ∑ k, ksVec (ksBasis n i) k * ksVec (ksBasis n j) k = 0 := by
  fin_cases n <;> fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | simp [ksVec, ksBasis, Fin.sum_univ_four]

/-- If exactly one of four booleans is `true`, then the corresponding `0`/`1` values
sum to `1`. -/
lemma sum_indicator_eq_one (g : Fin 4 → Bool) (h : ∃! i, g i = true) :
    ∑ i, (if g i then 1 else 0) = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hj
    have hgj : g j = false := by
      by_contra hc
      exact hj (hu j (by simpa using hc))
    simp [hgj]
  · simp

/-- **The Kochen–Specker theorem** (dimension 4).

There is no noncontextual `0`/`1` (here: `Bool`) valuation `f` of the vectors of `ℝ⁴`
such that every measurement context — every quadruple `b` of pairwise orthogonal
nonzero vectors, i.e. every orthogonal basis — contains exactly one vector valued `1`.

The proof exhibits the 18-vector / 9-basis configuration of
Cabello–Estebaranz–García-Alcaine and runs the parity argument. -/
theorem kochen_specker :
    ¬ ∃ f : (Fin 4 → ℝ) → Bool,
        ∀ b : Fin 4 → (Fin 4 → ℝ),
          (∀ i, b i ≠ 0) →
          (∀ i j, i ≠ j → ∑ k, b i k * b j k = 0) →
          ∃! i, f (b i) = true := by
  rintro ⟨f, hf⟩
  have key : ∀ n : Fin 9, ∑ i, (if f (ksVec (ksBasis n i)) then 1 else 0) = 1 := fun n =>
    sum_indicator_eq_one _
      (hf (fun i => ksVec (ksBasis n i)) (ksVec_ne_zero n) (ksBasis_orthogonal n))
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  have h6 := key 6
  have h7 := key 7
  have h8 := key 8
  simp only [Fin.sum_univ_four, ksBasis, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  -- Each of the eighteen vectors occurs in exactly two bases, so the nine equations
  -- sum to `2 * (total number of vectors valued 1) = 9`, which is impossible.
  omega

/-!
## Every dimension `n ≥ 4`

The dimension-4 result propagates to all higher dimensions.  The naive argument — embed
a 4-dimensional context into `ℝⁿ` by padding it with fixed standard basis vectors — is
not quite enough, because the valuation could put the value `1` on one of the padding
vectors and `0` on everything in the 4-dimensional block.  This is ruled out by first
looking at the standard basis context: exactly one standard basis vector `e_{i₀}` is
valued `1`, so choosing the 4-dimensional block to *contain* the coordinate `i₀` (by
conjugating with the transposition swapping `i₀` and `0`) makes every padding vector
valued `0`.
-/

variable {n : ℕ}

/-- The vector of `ℝⁿ` obtained from a vector of `ℝ⁴` by placing its coordinates in the
four coordinates of `ℝⁿ` that the permutation `τ` sends to `0, 1, 2, 3`, and filling the
remaining coordinates with `0`. -/
def padv (τ : Equiv.Perm (Fin n)) (v : Fin 4 → ℝ) : Fin n → ℝ :=
  fun k => if h : ((τ k : Fin n) : ℕ) < 4 then v ⟨τ k, h⟩ else 0

/-- The `j`-th standard basis vector of `ℝⁿ`. -/
def stdv (j : Fin n) : Fin n → ℝ := fun k => if k = j then 1 else 0

lemma padv_apply (hn : 4 ≤ n) (τ : Equiv.Perm (Fin n)) (v : Fin 4 → ℝ) (m : Fin 4) :
    padv τ v (τ.symm (Fin.castLE hn m)) = v m := by
  simp [padv]

lemma padv_eq_zero_of_not_lt (τ : Equiv.Perm (Fin n)) (v : Fin 4 → ℝ) {k : Fin n}
    (hk : ¬ ((τ k : Fin n) : ℕ) < 4) : padv τ v k = 0 := by
  simp [padv, hk]

lemma padv_ne_zero (hn : 4 ≤ n) (τ : Equiv.Perm (Fin n)) {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    padv τ v ≠ 0 := by
  obtain ⟨m, hm⟩ := Function.ne_iff.1 hv
  refine Function.ne_iff.2 ⟨τ.symm (Fin.castLE hn m), ?_⟩
  rw [padv_apply hn]
  simpa using hm

/-- Padding preserves inner products. -/
lemma padv_dot (hn : 4 ≤ n) (τ : Equiv.Perm (Fin n)) (u v : Fin 4 → ℝ) :
    ∑ k, padv τ u k * padv τ v k = ∑ m : Fin 4, u m * v m := by
  classical
  set G : ℕ → ℝ := fun m => if h : m < 4 then u ⟨m, h⟩ * v ⟨m, h⟩ else 0 with hG
  have h1 : ∑ k, padv τ u k * padv τ v k
      = ∑ j : Fin n, padv τ u (τ.symm j) * padv τ v (τ.symm j) :=
    (Equiv.sum_comp τ.symm (fun j => padv τ u j * padv τ v j)).symm
  have h2 : ∀ j : Fin n, padv τ u (τ.symm j) * padv τ v (τ.symm j) = G (j : ℕ) := by
    intro j
    by_cases h : (j : ℕ) < 4 <;> simp [padv, hG, h]
  rw [h1, Finset.sum_congr rfl (fun j _ => h2 j), Fin.sum_univ_eq_sum_range G n]
  have hsub : Finset.range 4 ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_range] at *
    omega
  have h3 : ∑ m ∈ Finset.range n, G m = ∑ m ∈ Finset.range 4, G m := by
    refine (Finset.sum_subset hsub ?_).symm
    intro m _ hm
    simp [hG, Finset.mem_range.not.1 hm]
  rw [h3, ← Fin.sum_univ_eq_sum_range G 4]
  exact Finset.sum_congr rfl (fun m _ => by simp [hG, m.isLt])

lemma sum_mul_stdv (g : Fin n → ℝ) (j : Fin n) : ∑ k, g k * stdv j k = g j := by
  simp [stdv, Finset.sum_ite_eq']

lemma sum_stdv_mul (g : Fin n → ℝ) (j : Fin n) : ∑ k, stdv j k * g k = g j := by
  simp [stdv, Finset.sum_ite_eq']

lemma sum_stdv_stdv {i j : Fin n} (hij : i ≠ j) : ∑ k, stdv i k * stdv j k = 0 := by
  rw [sum_stdv_mul]
  simp [stdv, hij]

lemma stdv_ne_zero (i : Fin n) : stdv i ≠ 0 := by
  refine Function.ne_iff.2 ⟨i, ?_⟩
  simp [stdv]

/-- **The Kochen–Specker theorem** in every dimension `n ≥ 4`: there is no noncontextual
`0`/`1` valuation of the vectors of `ℝⁿ` giving the value `1` to exactly one member of
every orthogonal basis. -/
theorem kochen_specker_dim_ge_four (hn : 4 ≤ n) :
    ¬ ∃ f : (Fin n → ℝ) → Bool,
        ∀ b : Fin n → (Fin n → ℝ),
          (∀ i, b i ≠ 0) →
          (∀ i j, i ≠ j → ∑ k, b i k * b j k = 0) →
          ∃! i, f (b i) = true := by
  rintro ⟨f, hf⟩
  -- Exactly one standard basis vector is valued `1`.
  obtain ⟨i0, hi0, hi0u⟩ := hf stdv (fun i => stdv_ne_zero i) (fun i j hij => sum_stdv_stdv hij)
  have hstdfalse : ∀ i : Fin n, i ≠ i0 → f (stdv i) = false := by
    intro i hi
    by_contra hc
    exact hi (hi0u i (by simpa using hc))
  -- Move the coordinate `i0` into the block of the first four coordinates.
  set z : Fin n := Fin.castLE hn (0 : Fin 4) with hz
  set τ : Equiv.Perm (Fin n) := Equiv.swap i0 z with hτ
  have hτi0 : τ i0 = z := by simp [hτ]
  refine kochen_specker ⟨fun v => f (padv τ v), ?_⟩
  intro b hb horth
  -- Extend the 4-dimensional context `b` by the standard basis vectors outside the block.
  set B : Fin n → (Fin n → ℝ) := fun i =>
    if h : ((τ i : Fin n) : ℕ) < 4 then padv τ (b ⟨τ i, h⟩) else stdv i with hB
  have hBne : ∀ i, B i ≠ 0 := by
    intro i
    by_cases h : ((τ i : Fin n) : ℕ) < 4
    · simpa [hB, h] using padv_ne_zero hn τ (hb ⟨τ i, h⟩)
    · simpa [hB, h] using stdv_ne_zero i
  have hBorth : ∀ i j, i ≠ j → ∑ k, B i k * B j k = 0 := by
    intro i j hij
    by_cases hi : ((τ i : Fin n) : ℕ) < 4 <;> by_cases hj : ((τ j : Fin n) : ℕ) < 4
    · have hne : (⟨τ i, hi⟩ : Fin 4) ≠ ⟨τ j, hj⟩ := by
        intro h
        exact hij (τ.injective (Fin.ext (by simpa using congrArg Fin.val h)))
      simp only [hB, dif_pos hi, dif_pos hj]
      rw [padv_dot hn]
      exact horth _ _ hne
    · simp only [hB, dif_pos hi, dif_neg hj]
      rw [sum_mul_stdv]
      exact padv_eq_zero_of_not_lt τ _ hj
    · simp only [hB, dif_neg hi, dif_pos hj]
      rw [sum_stdv_mul]
      exact padv_eq_zero_of_not_lt τ _ hi
    · simp only [hB, dif_neg hi, dif_neg hj]
      exact sum_stdv_stdv hij
  obtain ⟨i, hi, hiu⟩ := hf B hBne hBorth
  -- The unique member of the extended context valued `1` lies in the 4-dimensional block.
  have hib : ((τ i : Fin n) : ℕ) < 4 := by
    by_contra h
    have hii0 : i ≠ i0 := by
      rintro rfl
      exact h (by rw [hτi0, hz]; simp)
    rw [hB] at hi
    simp only [dif_neg h] at hi
    rw [hstdfalse i hii0] at hi
    exact Bool.noConfusion hi
  refine ⟨⟨τ i, hib⟩, ?_, ?_⟩
  · simpa [hB, dif_pos hib] using hi
  · intro q hq
    set iq : Fin n := τ.symm (Fin.castLE hn q) with hiq
    have hτiq : τ iq = Fin.castLE hn q := by simp [hiq]
    have hlt : ((τ iq : Fin n) : ℕ) < 4 := by rw [hτiq]; exact q.isLt
    have hval : ((τ iq : Fin n) : ℕ) = (q : ℕ) := by rw [hτiq]; simp
    have hidx : (⟨((τ iq : Fin n) : ℕ), hlt⟩ : Fin 4) = q := Fin.ext hval
    have hBiq : B iq = padv τ (b q) := by simp only [hB, dif_pos hlt, hidx]
    have hfiq : f (B iq) = true := by rw [hBiq]; exact hq
    have heq : iq = i := hiu iq hfiq
    have heq2 : Fin.castLE hn q = τ i := by rw [← hτiq, heq]
    exact Fin.ext (by simpa using congrArg Fin.val heq2)

end Frontier

