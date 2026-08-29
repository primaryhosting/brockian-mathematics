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

