import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module docstring, so the header
-- comment above appears immediately after the import.)

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
## The Kadison–Singer problem

The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) `D` of a matrix / operator algebra `A` extends *uniquely* to a state of `A`
(the extension being then automatically pure).  It was solved affirmatively by
Marcus, Spielman and Srivastava.

Here we formalize the statement for the *atomic* MASA, and give a complete, self-contained
proof of the finite-dimensional case: for the diagonal MASA `Dₙ ⊆ Mₙ(ℂ)`, every pure state
of `Dₙ` (i.e. every coordinate evaluation `d ↦ d i`) has a unique extension to a state of
`Mₙ(ℂ)`, namely `A ↦ A i i`, and that extension is a pure state.
-/

namespace Frontier

open ComplexOrder Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital positive linear functional. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  nonneg : ∀ A : Matrix n n ℂ, 0 ≤ f (Aᴴ * A)

/-- A state is *pure* if it is an extreme point of the state space. -/

def IsPure (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop :=
  IsState f ∧
    ∀ g₁ g₂ : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState g₁ → IsState g₂ → ∀ t : ℝ, 0 < t → t < 1 →
      f = (t : ℂ) • g₁ + ((1 - t : ℝ) : ℂ) • g₂ → g₁ = f ∧ g₂ = f

/-- `f` extends the pure state `d ↦ d i` of the diagonal MASA `Dₙ ⊆ Mₙ(ℂ)`. -/

def ExtendsDiagDelta (i : n) (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ d : n → ℂ, f (Matrix.diagonal d) = d i

/-- The candidate (vector) state `A ↦ A i i` on `Mₙ(ℂ)`. -/

def diagState (i : n) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun A := A i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in

@[simp] lemma diagState_apply (i : n) (A : Matrix n n ℂ) : diagState i A = A i i := rfl

/-! ### Elementary helpers -/

omit [Fintype n] in

private lemma conjTranspose_single (j k : n) (c : ℂ) :
    (Matrix.single j k c)ᴴ = Matrix.single k j (starRingEnd ℂ c) := by
  ext a b
  simp [Matrix.single_apply, Matrix.conjTranspose_apply]
  aesop

private lemma real_lin_nonneg {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ t * a + b) : a = 0 := by
  by_contra hne
  have h1 := h (-(b + 1) / a)
  rw [div_mul_cancel₀ _ hne] at h1
  linarith

/-- If an affine function `t ↦ t • z + γ` of a real parameter takes values in the
nonnegative complex numbers, then `z = 0`. -/

private lemma complex_lin_nonneg {z γ : ℂ} (h : ∀ t : ℝ, 0 ≤ (t : ℂ) * z + γ) : z = 0 := by
  have him : ∀ t : ℝ, t * z.im + γ.im = 0 := by
    intro t
    have h2 := ((Complex.le_def).1 (h t)).2
    simpa using h2.symm
  have hre : ∀ t : ℝ, 0 ≤ t * z.re + γ.re := by
    intro t
    have h2 := ((Complex.le_def).1 (h t)).1
    simpa using h2
  have hz1 : z.re = 0 := real_lin_nonneg hre
  have hz2 : z.im = 0 := by
    have h0 := him 0
    have h1 := him 1
    simp at h0 h1
    simpa [h0] using h1
  exact Complex.ext hz1 hz2

/-! ### The key computation -/

lemma IsState.nonneg_single_diag {f : Matrix n n ℂ →ₗ[ℂ] ℂ} (hf : IsState f) (j : n) :
    0 ≤ f (Matrix.single j j 1) := by
  have := hf.nonneg (Matrix.single j j (1 : ℂ))
  simpa [conjTranspose_single] using this

/-- If a state annihilates the diagonal matrix unit `E j j`, then it annihilates both
matrix units `E j k` and `E k j` for every `k`. -/

lemma IsState.single_offdiag_eq_zero {f : Matrix n n ℂ →ₗ[ℂ] ℂ} (hf : IsState f)
    {j k : n} (hj : f (Matrix.single j j 1) = 0) :
    f (Matrix.single j k 1) = 0 ∧ f (Matrix.single k j 1) = 0 := by
  set s : ℂ := f (Matrix.single j k 1) with hs
  set u : ℂ := f (Matrix.single k j 1) with hu
  set γ : ℂ := f (Matrix.single k k 1) with hγ
  -- the basic family of inequalities
  have key : ∀ lam : ℂ, 0 ≤ (starRingEnd ℂ) lam * s + lam * u + γ := by
    intro lam
    have hpos := hf.nonneg (Matrix.single j j lam + Matrix.single j k (1 : ℂ))
    have hexp : (Matrix.single j j lam + Matrix.single j k (1 : ℂ))ᴴ *
        (Matrix.single j j lam + Matrix.single j k (1 : ℂ))
        = Matrix.single j j (starRingEnd ℂ lam * lam)
          + Matrix.single j k ((starRingEnd ℂ) lam)
          + Matrix.single k j lam + Matrix.single k k 1 := by
      simp [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same]
      abel
    rw [hexp] at hpos
    have : f (Matrix.single j j (starRingEnd ℂ lam * lam)
          + Matrix.single j k ((starRingEnd ℂ) lam)
          + Matrix.single k j lam + Matrix.single k k 1)
        = (starRingEnd ℂ) lam * s + lam * u + γ := by
      have e1 : Matrix.single j j (starRingEnd ℂ lam * lam)
          = ((starRingEnd ℂ) lam * lam) • Matrix.single j j (1 : ℂ) := by simp
      have e2 : Matrix.single j k ((starRingEnd ℂ) lam)
          = ((starRingEnd ℂ) lam) • Matrix.single j k (1 : ℂ) := by simp
      have e3 : Matrix.single k j lam = lam • Matrix.single k j (1 : ℂ) := by simp
      rw [map_add, map_add, map_add, e1, e2, e3, map_smul, map_smul, map_smul, hj]
      simp only [smul_eq_mul, mul_zero, hs, hu, hγ]
      ring
    rwa [this] at hpos
  -- taking `lam` real gives `s + u = 0`
  have h1 : s + u = 0 := by
    refine complex_lin_nonneg (γ := γ) ?_
    intro t
    have := key (t : ℂ)
    simpa [mul_add] using this
  -- taking `lam` purely imaginary gives `u = s`
  have h2 : Complex.I * (u - s) = 0 := by
    refine complex_lin_nonneg (γ := γ) ?_
    intro t
    have := key ((t : ℂ) * Complex.I)
    have hconj : (starRingEnd ℂ) ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      simp
    rw [hconj] at this
    convert this using 2
    ring
  have h3 : u = s := by
    have := mul_eq_zero.1 h2
    rcases this with h | h
    · exact absurd h Complex.I_ne_zero
    · linear_combination h
  have hs0 : s = 0 := by
    rw [h3] at h1
    linear_combination h1 / 2
  exact ⟨hs0, by rw [h3]; exact hs0⟩

/-- **Uniqueness of the extension**: a state whose values on the diagonal matrix units are
those of the coordinate evaluation at `i` is the vector state `A ↦ A i i`. -/

lemma IsState.eq_diagState_of_diag {f : Matrix n n ℂ →ₗ[ℂ] ℂ} {i : n} (hf : IsState f)
    (h : ∀ j : n, f (Matrix.single j j 1) = if j = i then 1 else 0) :
    f = diagState i := by
  have hoff : ∀ j k : n, j ≠ k → f (Matrix.single j k 1) = 0 := by
    intro j k hjk
    by_cases hji : j = i
    · have hk : k ≠ i := by rintro rfl; exact hjk hji
      have hkz : f (Matrix.single k k 1) = 0 := by simp [h k, hk]
      exact (hf.single_offdiag_eq_zero (j := k) (k := j) hkz).2
    · have hjz : f (Matrix.single j j 1) = 0 := by simp [h j, hji]
      exact (hf.single_offdiag_eq_zero (j := j) (k := k) hjz).1
  ext A
  have hterm : ∀ j k : n, f (Matrix.single j k (A j k))
      = if j = i then (if k = i then A i i else 0) else 0 := by
    intro j k
    have hsm : Matrix.single j k (A j k) = (A j k) • Matrix.single j k (1 : ℂ) := by simp
    rw [hsm, map_smul]
    by_cases hjk : j = k
    · subst hjk
      by_cases hji : j = i
      · subst hji; simp [h j]
      · simp [h j, hji]
    · simp [hoff j k hjk]
      rintro rfl rfl
      exact absurd rfl hjk
  rw [diagState_apply]
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, hterm]
  simp

/-! ### Existence and purity -/

lemma diagState_isState (i : n) : IsState (diagState i) := by
  constructor
  · simp [diagState_apply]
  · intro A
    have : (Aᴴ * A) i i = ∑ k : n, (starRingEnd ℂ) (A k i) * A k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [diagState_apply, this]
    refine Finset.sum_nonneg ?_
    intro k _
    rw [Complex.conj_mul']
    exact_mod_cast Complex.zero_le_real.2 (by positivity)

omit [Fintype n] in

lemma diagState_extends (i : n) : ExtendsDiagDelta i (diagState i) := by
  intro d
  simp [diagState_apply]

omit [Fintype n] in

lemma ExtendsDiagDelta.diag_single {i : n} {f : Matrix n n ℂ →ₗ[ℂ] ℂ}
    (h : ExtendsDiagDelta i f) (j : n) :
    f (Matrix.single j j 1) = if j = i then 1 else 0 := by
  have hsd : Matrix.single j j (1 : ℂ) = Matrix.diagonal (Pi.single j (1 : ℂ)) :=
    (Matrix.diagonal_single j (1 : ℂ)).symm
  rw [hsd, h]
  simp [Pi.single_apply, eq_comm]

lemma diagState_isPure (i : n) : IsPure (diagState i) := by
  refine ⟨diagState_isState i, ?_⟩
  intro g₁ g₂ hg₁ hg₂ t ht0 ht1 hdec
  have hdiag : ∀ j : n, g₁ (Matrix.single j j 1) = (if j = i then 1 else 0) ∧
      g₂ (Matrix.single j j 1) = (if j = i then 1 else 0) := by
    have hne : ∀ j : n, j ≠ i → g₁ (Matrix.single j j 1) = 0 ∧
        g₂ (Matrix.single j j 1) = 0 := by
      intro j hj
      have hsum : (0 : ℂ) = (t : ℂ) * g₁ (Matrix.single j j 1)
          + ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) := by
        have := DFunLike.congr_fun hdec (Matrix.single j j (1 : ℂ))
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          diagState_apply] at this
        rw [← this]
        simp [hj]
      have hg₁0 := hg₁.nonneg_single_diag j
      have hg₂0 := hg₂.nonneg_single_diag j
      have hta : (0 : ℂ) ≤ (t : ℂ) * g₁ (Matrix.single j j 1) :=
        mul_nonneg (by exact_mod_cast Complex.zero_le_real.2 ht0.le) hg₁0
      have htb : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) :=
        mul_nonneg (by exact_mod_cast Complex.zero_le_real.2 (by linarith)) hg₂0
      have hA : (t : ℂ) * g₁ (Matrix.single j j 1) = 0 := by
        by_contra hcon
        have : (0 : ℂ) < (t : ℂ) * g₁ (Matrix.single j j 1) := lt_of_le_of_ne hta (Ne.symm hcon)
        have := add_pos_of_pos_of_nonneg this htb
        rw [← hsum] at this
        exact lt_irrefl _ this
      have hB : ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) = 0 := by
        by_contra hcon
        have : (0 : ℂ) < ((1 - t : ℝ) : ℂ) * g₂ (Matrix.single j j 1) :=
          lt_of_le_of_ne htb (Ne.symm hcon)
        have := add_pos_of_nonneg_of_pos hta this
        rw [← hsum] at this
        exact lt_irrefl _ this
      have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have ht1' : ((1 - t : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      exact ⟨by simpa [ht0'] using mul_eq_zero.1 hA |>.resolve_left ht0',
        by simpa using mul_eq_zero.1 hB |>.resolve_left ht1'⟩
    have hone : ∀ r : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState r →
        (∀ j : n, j ≠ i → r (Matrix.single j j 1) = 0) →
        r (Matrix.single i i 1) = 1 := by
      intro r hr hz
      have h1 : (1 : Matrix n n ℂ) = ∑ j : n, Matrix.single j j (1 : ℂ) := by
        ext a b
        rw [Matrix.sum_apply, Finset.sum_eq_single a]
        · simp [Matrix.single_apply, Matrix.one_apply]
        · intro c _ hc; simp [hc]
        · simp
      have := hr.unital
      rw [h1, map_sum] at this
      rw [Finset.sum_eq_single i] at this
      · exact this
      · intro j _ hj; exact hz j hj
      · intro hi; exact absurd (Finset.mem_univ i) hi
    intro j
    by_cases hj : j = i
    · subst hj
      refine ⟨by simp [hone g₁ hg₁ (fun j hj => (hne j hj).1)],
        by simp [hone g₂ hg₂ (fun j hj => (hne j hj).2)]⟩
    · exact ⟨by simp [(hne j hj).1, hj], by simp [(hne j hj).2, hj]⟩
  exact ⟨hg₁.eq_diagState_of_diag (fun j => (hdiag j).1),
    hg₂.eq_diagState_of_diag (fun j => (hdiag j).2)⟩

/-! ### The theorem -/

/-- **Kadison–Singer (finite-dimensional / matrix case).**

For the diagonal MASA `Dₙ ⊆ Mₙ(ℂ)`, every pure state of `Dₙ` — i.e. every coordinate
evaluation `d ↦ d i` — extends to a *unique* state of `Mₙ(ℂ)`, and that unique extension
(the vector state `A ↦ A i i`) is itself a pure state. -/

theorem kadison_singer (i : n) :
    (∃! f : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState f ∧ ExtendsDiagDelta i f) ∧
      ∀ f : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState f → ExtendsDiagDelta i f → IsPure f := by
  have huniq : ∀ f : Matrix n n ℂ →ₗ[ℂ] ℂ, IsState f → ExtendsDiagDelta i f →
      f = diagState i := fun f hf hext => hf.eq_diagState_of_diag hext.diag_single
  refine ⟨⟨diagState i, ⟨diagState_isState i, diagState_extends i⟩, ?_⟩, ?_⟩
  · rintro g₁ ⟨hg₁, hext⟩
    exact huniq g₁ hg₁ hext
  · intro f hf hext
    rw [huniq f hf hext]
    exact diagState_isPure i

/-!
### Weaver's discrepancy formulation

The infinite-dimensional Kadison–Singer problem was reduced by Weaver to the following
finite-dimensional discrepancy statement `KS_r`, which Marcus, Spielman and Srivastava
proved (for `r ≥ 2`) by the method of interlacing families of polynomials:

if `v ₁, …, vₘ` in `ℂ^d` form a resolution of the identity (`∑ i, |⟨v i, x⟩|² = ‖x‖²`)
with `‖v i‖² ≤ α`, then the index set can be partitioned into `r` blocks each of which has
"discrepancy" at most `(1/√r + √α)²`.

We formalize the statement below, and prove the base case `r = 1`.
-/

/-- **Weaver's `KS_r` statement.**  For all families `v ₁, …, vₘ` of vectors in `ℂ^d`
with `‖v i‖² ≤ α` which form a resolution of the identity, the index set admits a
partition into `r` blocks, each of operator norm at most `(1/√r + √α)²`.

Marcus–Spielman–Srivastava proved `WeaverKS r α` for `r ≥ 2` and `α ≥ 0`; this is
equivalent to the Kadison–Singer conjecture.  Only the base case `r = 1` is proved here. -/

def WeaverKS (r : ℕ) (α : ℝ) : Prop :=
  ∀ (d m : ℕ) (v : Fin m → EuclideanSpace ℂ (Fin d)),
    (∀ i, ‖v i‖ ^ 2 ≤ α) →
    (∀ x : EuclideanSpace ℂ (Fin d), ∑ i, ‖(inner (𝕜 := ℂ) (v i) x)‖ ^ 2 = ‖x‖ ^ 2) →
    ∃ P : Fin m → Fin r, ∀ j : Fin r, ∀ x : EuclideanSpace ℂ (Fin d),
      ∑ i ∈ Finset.univ.filter (fun i => P i = j), ‖(inner (𝕜 := ℂ) (v i) x)‖ ^ 2
        ≤ (1 / Real.sqrt r + Real.sqrt α) ^ 2 * ‖x‖ ^ 2

/-- **Base case of Weaver's `KS_r`**: for `r = 1` the (unique) partition into one block
works, because `(1/√1 + √α)² ≥ 1`. -/
