import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2

/-- The basis vector flipping coordinate `i`. -/
def flip {k : ℕ} (i : Fin k) : Cube k := Pi.single i 1

lemma flip_apply_self {k : ℕ} (i : Fin k) : flip i i = 1 := by
  simp [flip]

lemma flip_ne_zero {k : ℕ} (i : Fin k) : flip i ≠ 0 := by
  intro h
  have := congrArg (fun f => f i) h
  simp [flip_apply_self] at this

lemma add_self_cube {k : ℕ} (x : Cube k) : x + x = 0 := by
  ext j
  exact (by decide : ∀ a : ZMod 2, a + a = 0) (x j)

lemma add_right_cancel_cube {k : ℕ} (x y : Cube k) (h : x + y = 0) : x = y := by
  have := congrArg (fun t => t + y) h
  simpa [add_assoc, add_self_cube] using this

lemma flip_add_flip {k : ℕ} (i : Fin k) (x : Cube k) : x + flip i + flip i = x := by
  rw [add_assoc, add_self_cube, add_zero]

lemma flip_injective {k : ℕ} : Function.Injective (flip (k := k)) := by
  intro i j h
  by_contra hij
  have := congrArg (fun f => f i) h
  simp [flip, hij] at this

/-- The `k`-dimensional hypercube graph `Q_k`: two binary strings are adjacent iff they
differ in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i, y = x + flip i
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, (flip_add_flip i x).symm⟩
  loopless := by
    refine ⟨?_⟩
    rintro x ⟨i, h⟩
    exact flip_ne_zero i (by simpa using h.symm)

instance hypercubeDecidableAdj (k : ℕ) : DecidableRel (hypercube k).Adj := by
  intro x y
  exact inferInstanceAs (Decidable (∃ i, y = x + flip i))

lemma hypercube_neighborFinset (k : ℕ) (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.univ.image (fun i => x + flip i) := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube, eq_comm]

lemma hypercube_degree (k : ℕ) (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, hypercube_neighborFinset, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact flip_injective (by simpa using h)

lemma hypercube_lapMatrix_mulVec (k : ℕ) (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ *ᵥ v) x = k * v x - ∑ i, v (x + flip i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, hypercube_degree, hypercube_neighborFinset,
    Finset.sum_image]
  intro i _ j _ h
  exact flip_injective (by simpa using h)

/-! ### Characters of the hypercube -/

/-- The sign character of `ZMod 2`. -/
def sgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha | ha <;>
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b with hb | hb <;>
      norm_num [sgn, ha, hb, show (1 : ZMod 2) + 1 = 0 from rfl]

lemma sgn_ne_zero (a : ZMod 2) : sgn a ≠ 0 := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha | ha <;> simp [sgn, ha]

/-- The `ZMod 2`-valued inner product of two binary strings. -/
def dot {k : ℕ} (s x : Cube k) : ZMod 2 := ∑ i, s i * x i

lemma dot_add_right {k : ℕ} (s x y : Cube k) : dot s (x + y) = dot s x + dot s y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_add_left {k : ℕ} (s t x : Cube k) : dot (s + t) x = dot s x + dot t x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_flip_right {k : ℕ} (s : Cube k) (i : Fin k) : dot s (flip i) = s i := by
  simp [dot, flip, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

lemma dot_flip_left {k : ℕ} (s : Cube k) (i : Fin k) : dot (flip i) s = s i := by
  simp [dot, flip, Pi.single_apply, ite_mul, Finset.sum_ite_eq']

/-- The character of the hypercube indexed by `s`. -/
def chi {k : ℕ} (s x : Cube k) : ℝ := sgn (dot s x)

lemma chi_add_right {k : ℕ} (s x y : Cube k) : chi s (x + y) = chi s x * chi s y := by
  simp [chi, dot_add_right, sgn_add]

lemma chi_add_left {k : ℕ} (s t x : Cube k) : chi (s + t) x = chi s x * chi t x := by
  simp [chi, dot_add_left, sgn_add]

lemma chi_zero_right {k : ℕ} (s : Cube k) : chi s 0 = 1 := by
  simp [chi, dot, sgn]

lemma chi_ne_zero {k : ℕ} (s x : Cube k) : chi s x ≠ 0 := sgn_ne_zero _

/-- The number of coordinates where `s` is nonzero (the Hamming weight). -/
def wt {k : ℕ} (s : Cube k) : ℕ := (Finset.univ.filter (fun i => s i ≠ 0)).card

lemma sum_sgn_eq {k : ℕ} (s : Cube k) : ∑ i, sgn (s i) = (k : ℝ) - 2 * wt s := by
  have h : ∀ i : Fin k, sgn (s i) = 1 - 2 * (if s i ≠ 0 then (1 : ℝ) else 0) := by
    intro i
    by_cases h : s i = 0 <;> norm_num [sgn, h]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [wt, Finset.sum_ite, mul_comm]

/-- Orthogonality: the characters sum to `0` away from the origin. -/
lemma sum_chi (k : ℕ) (z : Cube k) :
    ∑ s : Cube k, chi s z = if z = 0 then (2 ^ k : ℝ) else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp [chi, dot, sgn]
  · rw [if_neg hz]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    have key : ∑ s : Cube k, chi s z = -∑ s : Cube k, chi s z := by
      calc ∑ s : Cube k, chi s z
          = ∑ s : Cube k, chi (s + flip j) z :=
            (Fintype.sum_equiv (Equiv.addRight (flip j)) _ _ (fun s => rfl)).symm
        _ = ∑ s : Cube k, -chi s z := by
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [chi_add_left]
            have : chi (flip j) z = -1 := by
              simp [chi, dot_flip_left, sgn, hj]
            rw [this]; ring
        _ = -∑ s : Cube k, chi s z := by rw [Finset.sum_neg_distrib]
    linarith [key]

/-- Fourier coefficients. -/
def fhat {k : ℕ} (f : Cube k → ℝ) (s : Cube k) : ℝ := ∑ x, f x * chi s x

lemma fourier_inversion {k : ℕ} (f : Cube k → ℝ) (x : Cube k) :
    ∑ s : Cube k, fhat f s * chi s x = 2 ^ k * f x := by
  have : ∀ s : Cube k, fhat f s * chi s x = ∑ y : Cube k, f y * chi s (y + x) := by
    intro s
    rw [fhat, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun y _ => by rw [chi_add_right]; ring)
  rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_comm]
  have h2 : ∀ y : Cube k, ∑ s : Cube k, f y * chi s (y + x)
      = f y * (if y + x = 0 then (2 ^ k : ℝ) else 0) := by
    intro y
    rw [← Finset.mul_sum, sum_chi]
  rw [Finset.sum_congr rfl (fun y _ => h2 y)]
  rw [Finset.sum_eq_single x]
  · rw [if_pos (add_self_cube x)]; ring
  · intro y _ hy
    have : y + x ≠ 0 := fun h => hy (add_right_cancel_cube y x h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ x) h

lemma fhat_eq_zero_iff {k : ℕ} (f : Cube k → ℝ) (h : ∀ s, fhat f s = 0) : f = 0 := by
  funext x
  have hinv := fourier_inversion f x
  rw [Finset.sum_congr rfl (fun s _ => by rw [h s]; ring : ∀ s ∈ Finset.univ,
    fhat f s * chi s x = (0 : ℝ))] at hinv
  rw [Finset.sum_const_zero] at hinv
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  have : f x = 0 := by
    rcases mul_eq_zero.mp hinv.symm with h1 | h1
    · exact absurd h1 hpow
    · exact h1
  simpa using this

/-- The characters are eigenvectors of the Laplacian, with eigenvalue twice the Hamming weight. -/
lemma lapMatrix_mulVec_chi (k : ℕ) (s : Cube k) :
    (hypercube k).lapMatrix ℝ *ᵥ chi s = (2 * wt s : ℝ) • chi s := by
  funext x
  rw [hypercube_lapMatrix_mulVec]
  have h : ∀ i : Fin k, chi s (x + flip i) = chi s x * sgn (s i) := by
    intro i
    rw [chi_add_right]
    simp [chi, dot_flip_right]
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum, sum_sgn_eq]
  simp [Pi.smul_apply]
  ring

/-- Fourier coefficients of the Laplacian applied to a vector. -/
lemma fhat_lapMatrix_mulVec {k : ℕ} (v : Cube k → ℝ) (s : Cube k) :
    fhat ((hypercube k).lapMatrix ℝ *ᵥ v) s = (2 * wt s : ℝ) * fhat v s := by
  have h : ∀ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ v) x * chi s x
      = (k : ℝ) * (v x * chi s x) - ∑ i, v (x + flip i) * chi s x := by
    intro x
    rw [hypercube_lapMatrix_mulVec, sub_mul, Finset.sum_mul]
    ring
  rw [fhat, Finset.sum_congr rfl (fun x _ => h x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_comm]
  have h2 : ∀ i : Fin k, ∑ x : Cube k, v (x + flip i) * chi s x = sgn (s i) * fhat v s := by
    intro i
    have : ∑ x : Cube k, v (x + flip i) * chi s x
        = ∑ y : Cube k, v y * chi s (y + flip i) :=
      Fintype.sum_equiv (Equiv.addRight (flip i)) _ _ (fun x => by
        simp only [Equiv.coe_addRight]
        rw [flip_add_flip])
    rw [this, fhat, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [chi_add_right]
    simp [chi, dot_flip_right]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.sum_mul, sum_sgn_eq, ← fhat]
  ring

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q_k` on `2 ^ k` vertices is exactly `2`.  In particular the family `(Q_k)` has a spectral gap
bounded below by `2`, uniformly in `k`. -/
theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k →
      IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : Cube k → ℝ, v ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} 2 := by
  intro k hk
  constructor
  · refine ⟨two_ne_zero, chi (flip ⟨0, hk⟩), ?_, ?_⟩
    · intro h
      exact chi_ne_zero (flip (⟨0, hk⟩ : Fin k)) 0 (by rw [h]; rfl)
    · have hw : wt (flip (⟨0, hk⟩ : Fin k)) = 1 := by
        rw [wt]
        rw [Finset.card_eq_one]
        refine ⟨⟨0, hk⟩, ?_⟩
        ext i
        simp [flip, Pi.single_apply, eq_comm]
      rw [lapMatrix_mulVec_chi, hw]
      norm_num
  · rintro μ ⟨hμ, v, hv, hLv⟩
    obtain ⟨s, hs⟩ : ∃ s, fhat v s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (fhat_eq_zero_iff v h)
    have h1 : μ * fhat v s = (2 * wt s : ℝ) * fhat v s := by
      rw [← fhat_lapMatrix_mulVec v s, hLv, fhat, fhat, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by simp [Pi.smul_apply]; ring)
    have h2 : μ = 2 * wt s := mul_right_cancel₀ hs h1
    have h3 : wt s ≠ 0 := by
      intro h
      rw [h2, h] at hμ
      simp at hμ
    have : 1 ≤ wt s := Nat.one_le_iff_ne_zero.mpr h3
    rw [h2]
    have : (1 : ℝ) ≤ (wt s : ℝ) := by exact_mod_cast this
    linarith

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/
theorem hypercube_card_vertices (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp

/-- The hypercube `Q_k` is `k`-regular. -/
theorem hypercube_regular (k : ℕ) (x : Cube k) : (hypercube k).degree x = k :=
  hypercube_degree k x

/-- **Uniform spectral gap.** Every nonzero Laplacian eigenvalue of `Q_k` is at least `2`,
with a bound that does not depend on `k`. -/
theorem hypercube_uniform_spectral_gap (k : ℕ) (μ : ℝ) (hμ : μ ≠ 0)
    (v : Cube k → ℝ) (hv : v ≠ 0) (hLv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) :
    2 ≤ μ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine absurd ?_ hv
    funext x
    have hx := congrFun hLv x
    rw [hypercube_lapMatrix_mulVec] at hx
    have : μ * v x = 0 := by simpa [Pi.smul_apply] using hx.symm
    simpa using (mul_eq_zero.mp this).resolve_left hμ
  · exact (expander_uniform_gap_witness k hk).2 ⟨hμ, v, hv, hLv⟩

end Frontier.Spectral

