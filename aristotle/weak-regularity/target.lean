import Mathlib

/-
  Brockian/WeylOperator.lean — the abstract symmetric-operator / (essential)
  self-adjointness scaffolding underneath the **Weyl criterion**, built over
  Mathlib's partially-defined linear maps `H →ₗ.[ℂ] H` (`LinearPMap`).

  ## Setting

  `H` is a complex inner product space (physics convention: `⟪·,·⟫` is
  conjugate-linear in the FIRST argument). An unbounded operator is a
  densely-defined `T : H →ₗ.[ℂ] H`. Mathlib v4.32.0 supplies `LinearPMap.adjoint`
  and `LinearPMap.IsFormalAdjoint`, but *no* `LinearPMap.IsSymmetric`, no
  deficiency indices, and no essential-self-adjointness predicate. This file
  builds that missing layer and proves the genuinely-load-bearing lemmas.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `IsSymmetric T`                 — `T` is symmetric iff it is its own formal
                                        adjoint (`T.IsFormalAdjoint T`), i.e.
                                        `⟪T x, y⟫ = ⟪x, T y⟫` on the domain.
    * `IsSymmetric.inner_apply`       — that defining bilinear identity, unpacked.
    * `IsSymmetric.inner_self_im`     — **the quadratic form is real**:
                                        `(⟪T v, v⟫).im = 0`. (Real-spectrum core.)
    * `IsSymmetric.im_eq_zero_of_apply_eq_smul`
                                      — **eigenvalues of a symmetric operator are
                                        real**: `T v = μ • v`, `v ≠ 0 ⇒ μ.im = 0`.
    * `IsSymmetric.norm_sub_smul_ge`  — **the basic symmetric-operator
                                        inequality** `‖T v − z·v‖ ≥ |Im z|·‖v‖`
                                        for every `z : ℂ`. This is THE key
                                        genuinely-provable analytic fact: it is
                                        the identity `‖(T−z)v‖² = ‖(T−Re z)v‖² +
                                        (Im z)²‖v‖²` in disguise.
    * `IsSymmetric.eq_zero_of_apply_eq_smul`
                                      — consequence: for `Im z ≠ 0`, `T − z` is
                                        **injective on the domain**
                                        (`T v = z • v ⇒ v = 0`). This is why the
                                        nonreal spectral parameter never meets the
                                        point spectrum of a symmetric operator.
    * `deficiencySpace T z`           — the **deficiency space** `ker(T* − z)`,
                                        defined honestly as the kernel of the
                                        linear map `f ↦ T* f − z·f` on `dom(T*)`.
    * `mem_deficiencySpace_iff`       — its defining characterization
                                        `g ∈ 𝒟_z ↔ T* g = z • g` (eigenvectors of
                                        the adjoint). The space is not `{0}` by
                                        fiat — it is a genuine kernel.
    * `EssentiallySelfAdjoint T`      — the **Weyl-criterion predicate**: both
                                        deficiency spaces `ker(T* ∓ i)` are
                                        trivial. The real definition, not `True`.
    * `smulPMap c` / `smulPMap_isSymmetric` / `smulPMap_apply`
                                      — **Gate-0 witness**: the everywhere-defined
                                        real-scalar operator `x ↦ c·x` (`c : ℝ`)
                                        is symmetric, instantiating the whole
                                        framework non-vacuously (`c = 1` is the
                                        identity). Its inequality and injectivity
                                        corollaries then hold by the theorems
                                        above.

  ## What is NOT proved, and why (honest scope statement)

  The Weyl criterion *itself* — "symmetric `T` is essentially self-adjoint iff
  both deficiency spaces vanish" — is **not** proved. It requires von Neumann's
  extension theory (the closure `T̄ = T**`, the Cayley transform, the
  identification of self-adjoint extensions with partial isometries between the
  deficiency spaces), none of which exists in Mathlib v4.32.0. Likewise we do
  not prove the bounded witness `smulPMap c` *is* essentially self-adjoint:
  that needs the adjoint of a `LinearMap.toPMap` computed explicitly (that
  `(smulPMap c)* = smulPMap c`), a `LinearPMap.adjoint` identity Mathlib does not
  provide. The predicate `EssentiallySelfAdjoint` is nonetheless the genuine
  mathematical one; this file ships the verified inequality/real-spectrum rung on
  which the criterion is built, and names nothing it does not prove.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Symmetric densely-defined operators -/

/-- **Symmetric operator.** A partially-defined operator `T : H →ₗ.[ℂ] H` is
*symmetric* when it is its own formal adjoint: `⟪T x, y⟫ = ⟪x, T y⟫` for all
`x, y` in the domain. This is the honest `LinearPMap` formulation (Mathlib has
`IsFormalAdjoint` but no `IsSymmetric`). -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

/-- The defining identity of a symmetric operator, unpacked. -/
theorem IsSymmetric.inner_apply {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (x y : T.domain) : ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := hT x y

/-- **The quadratic form of a symmetric operator is real.** For any `v` in the
domain, `⟪T v, v⟫` has zero imaginary part. This is the seed of the "spectrum is
real" phenomenon: from it both real eigenvalues and the basic inequality below
follow. -/
theorem IsSymmetric.inner_self_im {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) : (⟪T v, (v : H)⟫_ℂ).im = 0 := by
  have h1 : ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ := hT v v
  have h2 : (starRingEnd ℂ) ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ :=
    inner_conj_symm (v : H) (T v)
  rw [← h1] at h2
  rwa [Complex.conj_eq_iff_im] at h2

/-- **Eigenvalues of a symmetric operator are real.** If `T v = μ • v` for a
nonzero `v` in the domain, then `μ` is real (`μ.im = 0`). -/
theorem IsSymmetric.im_eq_zero_of_apply_eq_smul {T : H →ₗ.[ℂ] H}
    (hT : IsSymmetric T) {v : T.domain} {μ : ℂ} (hv : (v : H) ≠ 0)
    (heig : T v = μ • (v : H)) : μ.im = 0 := by
  have hb := hT.inner_self_im v
  rw [heig, inner_smul_left] at hb
  set s : ℂ := ⟪(v : H), (v : H)⟫_ℂ with hs
  have hsim : s.im = 0 := by
    have hc : (starRingEnd ℂ) s = s := inner_conj_symm (v : H) (v : H)
    rwa [Complex.conj_eq_iff_im] at hc
  have hsre : s.re = ‖(v : H)‖ ^ 2 := by rw [hs]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (v : H)
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hsim] at hb
  have hsrepos : (0 : ℝ) < s.re := by rw [hsre]; positivity
  have hz : μ.im * s.re = 0 := by linear_combination -hb
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hsrepos)

/-! ### The basic symmetric-operator inequality -/

/-- **The basic symmetric-operator inequality** `‖T v − z·v‖ ≥ |Im z|·‖v‖`.

For a symmetric `T`, every `z : ℂ`, and every `v` in the domain. This is the
analytic heart of the whole self-adjointness story: it is the Pythagorean
identity
    `‖(T − z)v‖² = ‖(T − Re z)v‖² + (Im z)²‖v‖²`
(valid because `⟪T v, v⟫` is real), from which we read off `≥ (Im z)²‖v‖²` and
take square roots. When `Im z ≠ 0` it forces `T − z` injective (below) and, in
the closed case, boundedly-invertible onto its range. -/
theorem IsSymmetric.norm_sub_smul_ge {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) (z : ℂ) : |z.im| * ‖(v : H)‖ ≤ ‖T v - z • (v : H)‖ := by
  set u : H := T v with hu
  set w : H := (v : H) with hw
  -- `⟪u, w⟫` is real (quadratic form of a symmetric operator)
  have hc : (⟪u, w⟫_ℂ).im = 0 := hT.inner_self_im v
  -- component identities for the complex scalar `z`
  have hnormz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  have hnormzr : ‖(z.re : ℂ)‖ = |z.re| := by simp
  -- expand both norms via the (RCLike) parallelogram/`norm_sub_sq` formula
  have e1 : ‖u - z • w‖ ^ 2 = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, z • w⟫_ℂ) + ‖z • w‖ ^ 2 :=
    norm_sub_sq u (z • w)
  have e2 : ‖u - (z.re : ℂ) • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, (z.re : ℂ) • w⟫_ℂ) + ‖(z.re : ℂ) • w‖ ^ 2 :=
    norm_sub_sq u _
  rw [inner_smul_right, norm_smul] at e1
  rw [inner_smul_right, norm_smul, hnormzr] at e2
  -- the real parts of the cross terms coincide (imaginary part of `⟪u,w⟫` drops out)
  have hr1 : RCLike.re (z * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show (z * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; ring
  have hr2 : RCLike.re ((z.re : ℂ) * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show ((z.re : ℂ) * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; simp
  rw [hr1] at e1; rw [hr2] at e2
  -- the Pythagorean split identity
  have key : ‖u - z • w‖ ^ 2 = ‖u - (z.re : ℂ) • w‖ ^ 2 + z.im ^ 2 * ‖w‖ ^ 2 := by
    rw [e1, e2]
    have ha : (‖z‖ * ‖w‖) ^ 2 = (z.re ^ 2 + z.im ^ 2) * ‖w‖ ^ 2 := by rw [mul_pow, hnormz]
    have hb : (|z.re| * ‖w‖) ^ 2 = z.re ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [ha, hb]; ring
  -- read off the squared inequality, then take square roots
  have hge : z.im ^ 2 * ‖w‖ ^ 2 ≤ ‖u - z • w‖ ^ 2 := by
    rw [key]; nlinarith [sq_nonneg ‖u - (z.re : ℂ) • w‖]
  have hA : (0 : ℝ) ≤ |z.im| * ‖w‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsq : (|z.im| * ‖w‖) ^ 2 = z.im ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
  calc |z.im| * ‖w‖ = Real.sqrt ((|z.im| * ‖w‖) ^ 2) := (Real.sqrt_sq hA).symm
    _ = Real.sqrt (z.im ^ 2 * ‖w‖ ^ 2) := by rw [hsq]
    _ ≤ Real.sqrt (‖u - z • w‖ ^ 2) := Real.sqrt_le_sqrt hge
    _ = ‖u - z • w‖ := Real.sqrt_sq (norm_nonneg _)

/-- **`T − z` is injective on the domain for nonreal `z`.** If `T` is symmetric,
`Im z ≠ 0`, and `T v = z • v`, then `v = 0`. Immediate from the basic inequality
(a nonzero eigenvector at `z` would force `|Im z|·‖v‖ ≤ 0`). -/
theorem IsSymmetric.eq_zero_of_apply_eq_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {z : ℂ} (hz : z.im ≠ 0) {v : T.domain} (h : T v = z • (v : H)) :
    (v : H) = 0 := by
  have hineq := hT.norm_sub_smul_ge v z
  rw [h, sub_self, norm_zero] at hineq
  have h1 : |z.im| * ‖(v : H)‖ = 0 :=
    le_antisymm hineq (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (abs_eq_zero.mp h2) hz
  · exact norm_eq_zero.mp h2

/-! ### Deficiency spaces and essential self-adjointness -/

section Adjoint

variable [CompleteSpace H]

/-- **The deficiency space `ker(T* − z)`.** For a densely-defined `T`, the
adjoint `T* = T.adjoint` is a `LinearPMap`; the deficiency space at `z` is the
kernel of the honest linear map `f ↦ T* f − z·f` on `dom(T*)`. It is *not*
`{0}` by fiat — it is a genuine kernel, and it measures the failure of essential
self-adjointness (Weyl / von Neumann). -/
noncomputable def deficiencySpace (T : H →ₗ.[ℂ] H) (z : ℂ) :
    Submodule ℂ T.adjoint.domain :=
  LinearMap.ker (T.adjoint.toFun - z • T.adjoint.domain.subtype)

/-- **Deficiency-space membership = eigenvector of the adjoint.**
`g ∈ ker(T* − z) ↔ T* g = z • g`. Confirms the definition is the real one. -/
theorem mem_deficiencySpace_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (g : T.adjoint.domain) :
    g ∈ deficiencySpace T z ↔ T.adjoint g = z • (g : H) := by
  rw [deficiencySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, sub_eq_zero]
  rfl

/-- **Essential self-adjointness (the Weyl-criterion predicate).** A symmetric
operator is essentially self-adjoint exactly when both deficiency spaces
`ker(T* ∓ i)` are trivial. This is the genuine predicate the Weyl limit-point
criterion certifies — not a placeholder. -/
def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop :=
  deficiencySpace T Complex.I = ⊥ ∧ deficiencySpace T (-Complex.I) = ⊥

end Adjoint

/-! ### Gate-0 witness: a concrete symmetric operator -/

/-- **The everywhere-defined real-scalar operator** `x ↦ (c : ℝ) • x`, packaged
as a `LinearPMap` with full domain `⊤`. For `c = 1` this is the identity. -/
noncomputable def smulPMap (c : ℝ) : H →ₗ.[ℂ] H := ((c : ℂ) • LinearMap.id).toPMap ⊤

/-- The witness acts as multiplication by the real scalar `c`. -/
@[simp] theorem smulPMap_apply (c : ℝ) (x : (smulPMap (H := H) c).domain) :
    (smulPMap c) x = (c : ℂ) • (x : H) := by
  simp [smulPMap, LinearMap.toPMap_apply]

/-- The witness is everywhere defined (domain `= ⊤`), hence densely defined. -/
theorem smulPMap_domain (c : ℝ) : (smulPMap (H := H) c).domain = ⊤ := by
  simp [smulPMap, LinearMap.toPMap]

/-- **Gate-0 (non-vacuity).** The real-scalar operator `smulPMap c` is symmetric,
instantiating `IsSymmetric` — and hence the inequality `norm_sub_smul_ge`, the
real-spectrum lemmas, and the injectivity corollary — on a genuine, nonzero
operator. So none of the framework is vacuous. -/
theorem smulPMap_isSymmetric (c : ℝ) : IsSymmetric (smulPMap (H := H) c) := by
  intro x y
  rw [smulPMap_apply, smulPMap_apply, inner_smul_left, inner_smul_right]
  simp

end Brockian.Weyl.Operator

/-
  Brockian/WeylBridge.lean — deficiency triviality for −y″ + V y = λ y
  at non-real λ (continuous real V; y, y' ∈ L²(ℝ)).

  Classical Wronskian identity: with
      W(x) = conj(y x) · y' x − conj(y' x) · y x,
  the ODE and reality of V give
      W' = −2i (Im λ) |y|².
  Since y, y' ∈ L², W' ∈ L¹ so W has limits at ±∞; the bound
      |W| ≤ |y|² + |y'|²
  forces those limits to vanish. Taking a → −∞, b → +∞ in the finite
  identity yields (Im λ) · ∫|y|² = 0, hence y ≡ 0 by continuity.
-/

open MeasureTheory Filter Topology intervalIntegral Set Complex ComplexConjugate

namespace Brockian.Weyl.Bridge

/-- `y` solves `−y″ + V y = λ y` on ℝ, with `y, y'` square-integrable. -/
structure IsL2Solution (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  deriv1 : ∀ x, HasDerivAt y (y' x) x
  deriv2 : ∀ x, HasDerivAt y' (y'' x) x
  eqn    : ∀ x, y'' x = ((V x : ℂ) - lam) * y x
  memL2  : MemLp y 2 volume
  memL2' : MemLp y' 2 volume

variable {V : ℝ → ℝ} {lam : ℂ} {y y' y'' : ℝ → ℂ}

/-! ### Regularity and integrability -/

theorem continuous_y (hy : IsL2Solution V lam y y' y'') : Continuous y :=
  continuous_iff_continuousAt.mpr fun x => (hy.deriv1 x).continuousAt

theorem continuous_y' (hy : IsL2Solution V lam y y' y'') : Continuous y' :=
  continuous_iff_continuousAt.mpr fun x => (hy.deriv2 x).continuousAt

theorem integrable_normSq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun x => ‖f x‖ ^ 2) := by
  simpa using hf.integrable_norm_rpow (by norm_num) (by norm_num)

theorem integrable_y_normSq (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => ‖y x‖ ^ 2) :=
  integrable_normSq hy.memL2

theorem integrable_y'_normSq (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => ‖y' x‖ ^ 2) :=
  integrable_normSq hy.memL2'

theorem integrable_normSq_add (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => ‖y x‖ ^ 2 + ‖y' x‖ ^ 2) :=
  (integrable_y_normSq hy).add (integrable_y'_normSq hy)

/-! ### Boundary Wronskian -/

/-- Boundary Wronskian of `(conj y, y)`. -/
noncomputable def wronskianConj (y y' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => conj (y x) * y' x - conj (y' x) * y x

theorem wronskianConj_eq_two_I_im (x : ℝ) :
    wronskianConj y y' x = (↑(2 * (conj (y x) * y' x).im) : ℂ) * I := by
  unfold wronskianConj
  have hz : conj (conj (y x) * y' x) = conj (y' x) * y x := by
    simp [map_mul, mul_comm]
  rw [← hz, Complex.sub_conj]

theorem norm_wronskianConj_le (x : ℝ) :
    ‖wronskianConj y y' x‖ ≤ ‖y x‖ ^ 2 + ‖y' x‖ ^ 2 := by
  have h1 : ‖wronskianConj y y' x‖ = 2 * |(conj (y x) * y' x).im| := by
    rw [wronskianConj_eq_two_I_im, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
  have h2 : |(conj (y x) * y' x).im| ≤ ‖y x‖ * ‖y' x‖ :=
    (Complex.abs_im_le_norm _).trans (by simp [norm_mul])
  have h3 : 2 * (‖y x‖ * ‖y' x‖) ≤ ‖y x‖ ^ 2 + ‖y' x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y x‖ - ‖y' x‖)]
  calc
    ‖wronskianConj y y' x‖ = 2 * |(conj (y x) * y' x).im| := h1
    _ ≤ 2 * (‖y x‖ * ‖y' x‖) := by gcongr
    _ ≤ ‖y x‖ ^ 2 + ‖y' x‖ ^ 2 := h3

/-! ### W' = −2i (Im λ) |y|² -/

theorem hasDerivAt_wronskianConj (hy : IsL2Solution V lam y y' y'') (x : ℝ) :
    HasDerivAt (wronskianConj y y')
      (-(2 * I * ↑lam.im) * ↑(‖y x‖ ^ 2)) x := by
  have h1 : HasDerivAt (fun t => conj (y t) * y' t)
      (conj (y' x) * y' x + conj (y x) * y'' x) x :=
    (hy.deriv1 x).star.mul (hy.deriv2 x)
  have h2 : HasDerivAt (fun t => conj (y' t) * y t)
      (conj (y'' x) * y x + conj (y' x) * y' x) x :=
    (hy.deriv2 x).star.mul (hy.deriv1 x)
  have hW0 : HasDerivAt (fun t => conj (y t) * y' t - conj (y' t) * y t)
      ((conj (y' x) * y' x + conj (y x) * y'' x)
        - (conj (y'' x) * y x + conj (y' x) * y' x)) x :=
    h1.sub h2
  have hsimp :
      (conj (y' x) * y' x + conj (y x) * y'' x)
        - (conj (y'' x) * y x + conj (y' x) * y' x)
      = conj (y x) * y'' x - conj (y'' x) * y x := by
    ring
  have hW : HasDerivAt (wronskianConj y y')
      (conj (y x) * y'' x - conj (y'' x) * y x) x := by
    change HasDerivAt (fun t => conj (y t) * y' t - conj (y' t) * y t) _ x
    rwa [hsimp] at hW0
  have hny : conj (y x) * y x = ↑(‖y x‖ ^ 2) := by
    rw [mul_comm, Complex.mul_conj, ofReal_inj, Complex.normSq_eq_norm_sq]
  have hcalc :
      conj (y x) * y'' x - conj (y'' x) * y x
        = (-(2 * I * ↑lam.im)) * ↑(‖y x‖ ^ 2) := by
    rw [hy.eqn x]
    simp only [map_mul, map_sub, Complex.conj_ofReal]
    -- goal: conj(y)*((V-λ)y) − (V−conj λ)·conj(y)·y = −(2i Im λ)·|y|²
    have hassoc :
        conj (y x) * (((V x : ℂ) - lam) * y x)
            - (↑(V x) - conj lam) * conj (y x) * y x
          = ((↑(V x) - lam) - (↑(V x) - conj lam)) * (conj (y x) * y x) := by
      ring
    rw [hassoc, hny]
    have hVdiff : (↑(V x) - lam) - (↑(V x) - conj lam) = -(2 * I * ↑lam.im) := by
      have : (↑(V x) - lam) - (↑(V x) - conj lam) = conj lam - lam := by ring
      rw [this, ← neg_sub, Complex.sub_conj]
      -- −↑(2 * lam.im) * I = −(2 * I * ↑lam.im)
      push_cast
      ring
    rw [hVdiff]
  exact hW.congr_deriv hcalc

theorem integrable_wronskianConj_deriv (hy : IsL2Solution V lam y y' y'') :
    Integrable (fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) := by
  simpa using (integrable_y_normSq hy).ofReal.const_mul (-(2 * I * ↑lam.im) : ℂ)

/-! ### Limits of W at ±∞ exist and vanish -/

theorem tendsto_wronskianConj_atTop
    (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atTop (nhds (limUnder atTop (wronskianConj y y'))) := by
  refine tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (a := 0) (f' := fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) ?_ ?_
  · intro x _hx; exact hasDerivAt_wronskianConj hy x
  · exact (integrable_wronskianConj_deriv hy).integrableOn

theorem tendsto_wronskianConj_atBot
    (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atBot (nhds (limUnder atBot (wronskianConj y y'))) := by
  refine tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic
    (a := 0) (f' := fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) ?_ ?_
  · intro x _hx; exact hasDerivAt_wronskianConj hy x
  · exact (integrable_wronskianConj_deriv hy).integrableOn

theorem not_integrableOn_const_pos_Ici {c A : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun _ : ℝ => c) (Ici A) := by
  intro h
  rw [IntegrableOn, integrable_const_iff] at h
  rcases h with rfl | hfin
  · exact lt_irrefl 0 hc
  · exact (isFiniteMeasure_restrict (μ := volume) (s := Ici A)).mp hfin Real.volume_Ici

theorem not_integrableOn_const_pos_Iic {c A : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun _ : ℝ => c) (Iic A) := by
  intro h
  rw [IntegrableOn, integrable_const_iff] at h
  rcases h with rfl | hfin
  · exact lt_irrefl 0 hc
  · exact (isFiniteMeasure_restrict (μ := volume) (s := Iic A)).mp hfin Real.volume_Iic

theorem limUnder_wronskianConj_atTop_eq_zero
    (hy : IsL2Solution V lam y y' y'') :
    limUnder atTop (wronskianConj y y') = 0 := by
  set L := limUnder atTop (wronskianConj y y')
  set g : ℝ → ℝ := fun x => ‖y x‖ ^ 2 + ‖y' x‖ ^ 2
  have hgI : Integrable g := integrable_normSq_add hy
  have htend := tendsto_wronskianConj_atTop hy
  by_contra hne
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hne
  have hEven : ∀ᶠ x in atTop, ‖L‖ / 2 ≤ ‖wronskianConj y y' x‖ := by
    have : Tendsto (fun x => ‖wronskianConj y y' x‖) atTop (nhds ‖L‖) := htend.norm
    filter_upwards [this.eventually_const_lt (half_lt_self hLpos)] with x hx
    exact hx.le
  have hmaj : ∀ᶠ x in atTop, ‖L‖ / 2 ≤ g x := by
    filter_upwards [hEven] with x hx
    exact hx.trans (norm_wronskianConj_le x)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hmaj
  have hOn : IntegrableOn g (Ici A) := hgI.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => ‖L‖ / 2) (Ici A) := by
    refine Integrable.mono' hOn continuous_const.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ici]
    refine Eventually.of_forall fun x hx => ?_
    simp only [Real.norm_eq_abs, abs_of_nonneg (half_pos hLpos).le]
    exact hA x hx
  exact not_integrableOn_const_pos_Ici (half_pos hLpos) hconst

theorem limUnder_wronskianConj_atBot_eq_zero
    (hy : IsL2Solution V lam y y' y'') :
    limUnder atBot (wronskianConj y y') = 0 := by
  set L := limUnder atBot (wronskianConj y y')
  set g : ℝ → ℝ := fun x => ‖y x‖ ^ 2 + ‖y' x‖ ^ 2
  have hgI : Integrable g := integrable_normSq_add hy
  have htend := tendsto_wronskianConj_atBot hy
  by_contra hne
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hne
  have hEven : ∀ᶠ x in atBot, ‖L‖ / 2 ≤ ‖wronskianConj y y' x‖ := by
    have : Tendsto (fun x => ‖wronskianConj y y' x‖) atBot (nhds ‖L‖) := htend.norm
    filter_upwards [this.eventually_const_lt (half_lt_self hLpos)] with x hx
    exact hx.le
  have hmaj : ∀ᶠ x in atBot, ‖L‖ / 2 ≤ g x := by
    filter_upwards [hEven] with x hx
    exact hx.trans (norm_wronskianConj_le x)
  obtain ⟨A, hA⟩ := eventually_atBot.mp hmaj
  have hOn : IntegrableOn g (Iic A) := hgI.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => ‖L‖ / 2) (Iic A) := by
    refine Integrable.mono' hOn continuous_const.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Iic]
    refine Eventually.of_forall fun x hx => ?_
    simp only [Real.norm_eq_abs, abs_of_nonneg (half_pos hLpos).le]
    exact hA x hx
  exact not_integrableOn_const_pos_Iic (half_pos hLpos) hconst

theorem tendsto_wronskianConj_atTop_zero (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atTop (nhds 0) := by
  simpa [limUnder_wronskianConj_atTop_eq_zero hy] using tendsto_wronskianConj_atTop hy

theorem tendsto_wronskianConj_atBot_zero (hy : IsL2Solution V lam y y' y'') :
    Tendsto (wronskianConj y y') atBot (nhds 0) := by
  simpa [limUnder_wronskianConj_atBot_eq_zero hy] using tendsto_wronskianConj_atBot hy

/-! ### Finite-interval identity -/

theorem integral_wronskianConj_eq (hy : IsL2Solution V lam y y' y'') (a b : ℝ) :
    wronskianConj y y' b - wronskianConj y y' a
      = ∫ x in a..b, (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2) := by
  have hder : ∀ x ∈ uIcc a b, HasDerivAt (wronskianConj y y')
      ((-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) x := fun x _ =>
    hasDerivAt_wronskianConj hy x
  have hcont : Continuous (fun x => (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)) :=
    continuous_const.mul (continuous_ofReal.comp ((continuous_y hy).norm.pow 2))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hcont.intervalIntegrable a b)).symm

theorem integral_wronskianConj_eq_mul (hy : IsL2Solution V lam y y' y'') (a b : ℝ) :
    wronskianConj y y' b - wronskianConj y y' a
      = (-(2 * I * ↑lam.im) : ℂ) * ↑(∫ x in a..b, ‖y x‖ ^ 2) := by
  rw [integral_wronskianConj_eq hy a b]
  have h1 : ∫ x in a..b, (-(2 * I * ↑lam.im) : ℂ) * ↑(‖y x‖ ^ 2)
      = (-(2 * I * ↑lam.im) : ℂ) * ∫ x in a..b, (↑(‖y x‖ ^ 2) : ℂ) :=
    intervalIntegral.integral_const_mul _ _
  have h2 : ∫ x in a..b, (↑(‖y x‖ ^ 2) : ℂ) = ↑(∫ x in a..b, ‖y x‖ ^ 2) :=
    intervalIntegral.integral_ofReal
  rw [h1, h2]

/-! ### Passage to the whole line -/

theorem coeff_ne_zero (hlam : lam.im ≠ 0) : (-(2 * I * ↑lam.im) : ℂ) ≠ 0 := by
  intro h
  have h' : (2 * I * ↑lam.im : ℂ) = 0 := by
    have := congrArg Neg.neg h
    simpa using this
  have h2I : (2 * I : ℂ) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h2 | hI
    · norm_num at h2
    · exact Complex.I_ne_zero hI
  have him : (↑lam.im : ℂ) = 0 := (mul_eq_zero.mp h').resolve_left h2I
  exact hlam (ofReal_eq_zero.mp him)

theorem global_boundary_identity (hy : IsL2Solution V lam y y' y'') :
    (-(2 * I * ↑lam.im) : ℂ) * ↑(∫ x, ‖y x‖ ^ 2) = 0 := by
  let c : ℂ := -(2 * I * ↑lam.im)
  have hfin (n : ℕ) :
      wronskianConj y y' (n : ℝ) - wronskianConj y y' (-(n : ℝ))
        = c * ↑(∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2) :=
    integral_wronskianConj_eq_mul hy _ _
  have hL : Tendsto (fun n : ℕ => wronskianConj y y' (n : ℝ)) atTop (nhds 0) :=
    (tendsto_wronskianConj_atTop_zero hy).comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n : ℕ => wronskianConj y y' (-(n : ℝ))) atTop (nhds 0) := by
    have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    exact (tendsto_wronskianConj_atBot_zero hy).comp hneg
  have hLHS : Tendsto (fun n : ℕ =>
      wronskianConj y y' (n : ℝ) - wronskianConj y y' (-(n : ℝ))) atTop (nhds 0) := by
    simpa using hL.sub hR
  have hint : Integrable (fun x => ‖y x‖ ^ 2) := integrable_y_normSq hy
  have hInt : Tendsto (fun n : ℕ => ∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2)
      atTop (nhds (∫ x, ‖y x‖ ^ 2)) :=
    intervalIntegral_tendsto_integral hint
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      tendsto_natCast_atTop_atTop
  have hRHS : Tendsto (fun n : ℕ =>
      c * ↑(∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2))
      atTop (nhds (c * ↑(∫ x, ‖y x‖ ^ 2))) :=
    ((continuous_const.mul continuous_ofReal).tendsto _).comp hInt
  have hLHS' : Tendsto (fun n : ℕ =>
      c * ↑(∫ x in (-(n : ℝ))..(n : ℝ), ‖y x‖ ^ 2)) atTop (nhds 0) :=
    (tendsto_congr hfin).1 hLHS
  exact (tendsto_nhds_unique hLHS' hRHS).symm

/-! ### Main theorem -/

/-- **Deficiency triviality.** For continuous (bounded) real potential and non-real
spectral parameter, any global L² solution of `−y″ + V y = λ y` is identically zero. -/
theorem no_nonzero_L2_solution (V : ℝ → ℝ) (_hVc : Continuous V)
    (M : ℝ) (_hV : ∀ x, |V x| ≤ M) (lam : ℂ) (hlam : lam.im ≠ 0)
    (y y' y'' : ℝ → ℂ) (hy : IsL2Solution V lam y y' y'') :
    ∀ x, y x = 0 := by
  have hglob := global_boundary_identity (V := V) (lam := lam) (y := y) (y' := y')
    (y'' := y'') hy
  have hcoeff := coeff_ne_zero (lam := lam) hlam
  have hmassℂ : ↑(∫ x, ‖y x‖ ^ 2) = (0 : ℂ) :=
    (mul_eq_zero.mp hglob).resolve_left hcoeff
  have hmass : (∫ x, ‖y x‖ ^ 2 : ℝ) = 0 := ofReal_eq_zero.mp hmassℂ
  have hnn : 0 ≤ fun x : ℝ => ‖y x‖ ^ 2 := fun x => sq_nonneg _
  have hint : Integrable (fun x => ‖y x‖ ^ 2) := integrable_y_normSq hy
  have hae : (fun x => ‖y x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hint).mp hmass
  have hcont : Continuous (fun x => ‖y x‖ ^ 2) := (continuous_y hy).norm.pow 2
  have heq : (fun x => ‖y x‖ ^ 2) = fun _ => 0 :=
    (hcont.ae_eq_iff_eq volume continuous_zero).mp hae
  intro x
  have : ‖y x‖ ^ 2 = 0 := congrFun heq x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)

end Brockian.Weyl.Bridge

/-
  Brockian/WeylCayley.lean — the **Cayley-transform / essential-self-adjointness
  criterion** for symmetric unbounded operators, the capstone von Neumann piece
  sitting on top of `Brockian/WeylOperator.lean` (namespace `Brockian.Weyl.Operator`).

  ## Setting

  `T : H →ₗ.[ℂ] H` is a densely-defined symmetric operator on a complex Hilbert
  space `H` (physics convention: `⟪·,·⟫` conjugate-linear in the FIRST slot).
  Mathlib v4.32.0 supplies `LinearPMap.adjoint` with its fundamental property
  `⟪T† g, x⟫ = ⟪g, T x⟫` (`adjoint_isFormalAdjoint`), `mem_adjoint_domain_of_exists`,
  and `adjoint_apply_eq`, but **none** of the deficiency/Cayley layer below.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

    * `rangeSMulSub T w`              — the range submodule `ran(T − w) =
                                        {T v − w·v : v ∈ dom T}` (`Submodule ℂ H`),
                                        with membership lemma `mem_rangeSMulSub`.

    * `mem_orthogonal_rangeSMulSub_iff`
                                      — **THE von Neumann orthogonality identity**
                                        `ker(T* − z) = (ran(T − z̄))ᗮ`, in the form
                                        `g ∈ (ran(T − z̄))ᗮ ↔ ∃ hg, T* ⟨g,hg⟩ = z·g`.
                                        Proved directly from the adjoint's defining
                                        relation `⟪T* g, x⟫ = ⟪g, T x⟫` via
                                        `mem_adjoint_domain_of_exists` and
                                        `adjoint_apply_eq`. This is the genuine
                                        inner-product content of the criterion.

    * `deficiencySpace_eq_bot_iff`    — the deficiency space `ker(T* − z)` is
                                        trivial iff `ran(T − z̄)` is dense in `H`
                                        (bridges the subtype-valued kernel to a
                                        density statement, via
                                        `topologicalClosure_eq_top_iff`:
                                        `Kᗮ = ⊥ ↔ Dense K`).

    * `essentiallySelfAdjoint_iff`    — **THE CRITERION.** A densely-defined
                                        symmetric operator is essentially
                                        self-adjoint iff both `ran(T + i)` and
                                        `ran(T − i)` are dense:
                                        `EssentiallySelfAdjoint T ↔
                                          Dense (ran(T+i)) ∧ Dense (ran(T−i))`.
                                        The full Weyl / von Neumann deficiency
                                        criterion — a genuine ⟺, not a
                                        restatement of the predicate.

    * `norm_add_I_smul_eq`            — **the Cayley isometry (norm form)**
                                        `‖T v + i·v‖ = ‖T v − i·v‖` for `v ∈ dom T`,
                                        `T` symmetric. Exactly the statement that
                                        the Cayley map `V : (T−i)v ↦ (T+i)v`
                                        preserves norm (its isometry content): the
                                        `±i` cross terms cancel because `⟪T v, v⟫`
                                        is real. Proved from the
                                        `norm_add_sq`/`norm_sub_sq` expansion.

    * `apply_ne_I_smul` / `apply_ne_neg_I_smul`
                                      — injectivity of `T ± i` on the domain
                                        (`±i` are never eigenvalues of a symmetric
                                        operator), so `V` is well-defined.

  ## Scope

  `essentiallySelfAdjoint_iff` is the FULL rung: a real ⟺ whose forward/backward
  work is carried by the orthogonality identity `mem_orthogonal_rangeSMulSub_iff`,
  which does honest inner-product computation with the adjoint. Not built (and not
  needed for the criterion): the bundled `LinearIsometry` object for the Cayley
  transform (choosing preimages of `ran(T−i)`, packaging linearity) and the
  closure / self-adjoint-extension theory `T̄ = T**`, both absent from Mathlib
  v4.32.0. `norm_add_I_smul_eq` is the isometry's mathematical content; the bundled
  map is deferred.

  Verification (spec §2A): AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Brockian.Weyl.Cayley

open scoped InnerProductSpace
open Brockian.Weyl.Operator LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### The range submodule `ran(T − w)` -/

/-- **The range submodule** `ran(T − w) = {T v − w·v : v ∈ dom T}` as a
`Submodule ℂ H`, built from the honest linear map `v ↦ T v − w·v` on `dom T`. -/
noncomputable def rangeSMulSub (T : H →ₗ.[ℂ] H) (w : ℂ) : Submodule ℂ H :=
  LinearMap.range (T.toFun - w • T.domain.subtype)

/-- Membership in `ran(T − w)`: `u ∈ ran(T − w) ↔ ∃ v ∈ dom T, T v − w·v = u`. -/
theorem mem_rangeSMulSub {T : H →ₗ.[ℂ] H} {w : ℂ} {u : H} :
    u ∈ rangeSMulSub T w ↔ ∃ v : T.domain, T v - w • (v : H) = u := by
  rw [rangeSMulSub, LinearMap.mem_range]
  constructor <;> · rintro ⟨v, hv⟩; exact ⟨v, by simpa using hv⟩

/-! ### The von Neumann orthogonality identity -/

section Adjoint

variable [CompleteSpace H]

/-- **The von Neumann orthogonality identity** `ker(T* − z) = (ran(T − z̄))ᗮ`.

For a densely-defined `T`, a vector `g` lies in the orthogonal complement of the
range of `T − z̄` exactly when `g` belongs to the domain of the adjoint and is an
eigenvector `T* g = z·g`. This identifies the deficiency space `ker(T* − z)` with
the closed subspace `(ran(T − z̄))ᗮ`, whence "deficiency trivial ⟺ range dense".
Proved directly from the adjoint's fundamental property `⟪T* g, x⟫ = ⟪g, T x⟫`. -/
theorem mem_orthogonal_rangeSMulSub_iff {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) (z : ℂ) (g : H) :
    g ∈ (rangeSMulSub T (starRingEnd ℂ z))ᗮ ↔
      ∃ hg : g ∈ T.adjoint.domain, T.adjoint ⟨g, hg⟩ = z • g := by
  constructor
  · -- `g ⊥ ran(T − z̄)` gives `⟪g, T v⟫ = z̄·⟪g, v⟫`, so `g ∈ dom T*` and `T* g = z·g`
    intro hg
    have hortho : ∀ v : T.domain, ⟪g, T v⟫_ℂ = (starRingEnd ℂ z) * ⟪g, (v : H)⟫_ℂ := by
      intro v
      have hz := (Submodule.mem_orthogonal' _ g).mp hg
        (T v - (starRingEnd ℂ z) • (v : H)) (mem_rangeSMulSub.mpr ⟨v, rfl⟩)
      rw [inner_sub_right, inner_smul_right, sub_eq_zero] at hz
      exact hz
    have hg' : g ∈ T.adjoint.domain := by
      apply mem_adjoint_domain_of_exists
      refine ⟨z • g, fun x => ?_⟩
      rw [inner_smul_left, hortho x]
    refine ⟨hg', ?_⟩
    apply adjoint_apply_eq hT
    intro x
    rw [inner_smul_left]
    exact (hortho x).symm
  · -- eigenvector of `T*` at `z` ⇒ orthogonal to `ran(T − z̄)`
    rintro ⟨hg, heig⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨v, rfl⟩ := mem_rangeSMulSub.mp hu
    rw [inner_sub_right, inner_smul_right, sub_eq_zero]
    have hfa := adjoint_isFormalAdjoint hT ⟨g, hg⟩ v
    rw [heig, inner_smul_left] at hfa
    exact hfa.symm

/-- **Deficiency space trivial ⟺ range dense.** `ker(T* − z) = ⊥` exactly when
`ran(T − z̄)` is dense in `H`. Combines the orthogonality identity with
`topologicalClosure_eq_top_iff` (`Kᗮ = ⊥ ↔ closure K = ⊤ ↔ Dense K`), bridging the
subtype-valued deficiency space to a density statement in `H`. -/
theorem deficiencySpace_eq_bot_iff {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) (z : ℂ) :
    deficiencySpace T z = ⊥ ↔ Dense (rangeSMulSub T (starRingEnd ℂ z) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff, Submodule.eq_bot_iff]
  constructor
  · intro h g hg
    obtain ⟨hgd, heig⟩ := (mem_orthogonal_rangeSMulSub_iff hT z g).mp hg
    have h0 : (⟨g, hgd⟩ : T.adjoint.domain) = 0 :=
      h ⟨g, hgd⟩ ((mem_deficiencySpace_iff T z ⟨g, hgd⟩).mpr heig)
    simpa using congrArg Subtype.val h0
  · intro h g hg
    have heig := (mem_deficiencySpace_iff T z g).mp hg
    have hmem : (g : H) ∈ (rangeSMulSub T (starRingEnd ℂ z))ᗮ :=
      (mem_orthogonal_rangeSMulSub_iff hT z (g : H)).mpr ⟨g.2, heig⟩
    exact Subtype.ext (h (g : H) hmem)

/-! ### The essential-self-adjointness criterion -/

/-- `ran(T + i) = {T v + i·v : v ∈ dom T}` (the Cayley denominator's range). -/
noncomputable def rangeAddI (T : H →ₗ.[ℂ] H) : Submodule ℂ H := rangeSMulSub T (-Complex.I)

/-- `ran(T − i) = {T v − i·v : v ∈ dom T}` (the Cayley numerator's range). -/
noncomputable def rangeSubI (T : H →ₗ.[ℂ] H) : Submodule ℂ H := rangeSMulSub T Complex.I

/-- **THE ESSENTIAL-SELF-ADJOINTNESS CRITERION (Weyl / von Neumann).**

A densely-defined symmetric operator `T` is essentially self-adjoint **iff** both
`ran(T + i)` and `ran(T − i)` are dense in `H`. Equivalently, both deficiency
spaces `ker(T* ∓ i)` are trivial. Obtained by applying the orthogonality identity
at `z = i` (`z̄ = −i`, giving `ran(T + i)`) and at `z = −i` (`z̄ = i`, giving
`ran(T − i)`). -/
theorem essentiallySelfAdjoint_iff {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H)) :
    EssentiallySelfAdjoint T ↔
      Dense (rangeAddI T : Set H) ∧ Dense (rangeSubI T : Set H) := by
  unfold EssentiallySelfAdjoint
  rw [deficiencySpace_eq_bot_iff hT, deficiencySpace_eq_bot_iff hT, rangeAddI, rangeSubI,
      show (starRingEnd ℂ) Complex.I = -Complex.I from Complex.conj_I,
      show (starRingEnd ℂ) (-Complex.I) = Complex.I by
        rw [_root_.map_neg, Complex.conj_I, neg_neg]]

end Adjoint

/-! ### The Cayley isometry (norm form) and injectivity of `T ± i` -/

/-- **The Cayley isometry, norm form:** `‖T v + i·v‖ = ‖T v − i·v‖` for `v` in the
domain of a symmetric operator `T`. This says the Cayley map `V : (T−i)v ↦ (T+i)v`
preserves norm — the analytic heart of `V : ran(T−i) → ran(T+i)` being an isometry.
The cross terms `±2·Re⟪T v, i·v⟫` cancel because `⟪T v, v⟫` is real
(`IsSymmetric.inner_self_im`), so the two squared norms coincide. -/
theorem norm_add_I_smul_eq {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) (v : T.domain) :
    ‖T v + Complex.I • (v : H)‖ = ‖T v - Complex.I • (v : H)‖ := by
  set u : H := T v with hu
  set w : H := (v : H) with hw
  have hc : (⟪u, w⟫_ℂ).im = 0 := hT.inner_self_im v
  have hre : RCLike.re (⟪u, Complex.I • w⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    show (Complex.I * ⟪u, w⟫_ℂ).re = 0
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, hc]; ring
  have e1 : ‖u + Complex.I • w‖ ^ 2
      = ‖u‖ ^ 2 + 2 * RCLike.re (⟪u, Complex.I • w⟫_ℂ) + ‖Complex.I • w‖ ^ 2 :=
    norm_add_sq u _
  have e2 : ‖u - Complex.I • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, Complex.I • w⟫_ℂ) + ‖Complex.I • w‖ ^ 2 :=
    norm_sub_sq u _
  have hsq : ‖u + Complex.I • w‖ ^ 2 = ‖u - Complex.I • w‖ ^ 2 := by rw [e1, e2, hre]; ring
  have hfin := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hfin

/-- **`T + i` is injective on the domain.** `i` is never an eigenvalue of a
symmetric operator: `T v = i·v ⇒ v = 0`. (So the Cayley factor, here in `+i` form,
is injective and `V` is well-defined.) -/
theorem apply_ne_I_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {v : T.domain}
    (h : T v = Complex.I • (v : H)) : (v : H) = 0 :=
  hT.eq_zero_of_apply_eq_smul (by rw [Complex.I_im]; exact one_ne_zero) h

/-- **`T − i` is injective on the domain.** `−i` is never an eigenvalue of a
symmetric operator: `T v = −i·v ⇒ v = 0`. -/
theorem apply_ne_neg_I_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {v : T.domain}
    (h : T v = (-Complex.I) • (v : H)) : (v : H) = 0 :=
  hT.eq_zero_of_apply_eq_smul
    (by rw [Complex.neg_im, Complex.I_im]; exact neg_ne_zero.mpr one_ne_zero) h

end Brockian.Weyl.Cayley

/-
  Brockian/WeylChain.lean — closing the Weyl chain, modulo the one open link.

  The essential-self-adjointness chain for a densely-defined symmetric operator T:

    finite-b nested-circle geometry   (Brockian.Weyl.Disk, VERIFIED)
        │  radius r_b = 1/(2|Im λ|∫₀ᵇ|φ|²), monotone
        ▼
    b→∞ dichotomy  r_b→0 ⟺ ∫₀^∞|φ|²=∞   (Aristotle target: aristotle/…/WeylDichotomyTarget.lean)
        ▼
    limit-point at ∞                     (Brockian.Weyl.LP: const potential VERIFIED; general OPEN)
        │  ⟵── THE ONE OPEN LINK: limit-point ⟹ ran(T±i) dense ──⟶
        ▼
    ran(T+i), ran(T−i) both dense
        ▼
    EssentiallySelfAdjoint T             (Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff, VERIFIED)

  This file proves the LOWER half unconditionally: given the two range-density facts,
  essential self-adjointness follows from the verified von Neumann criterion. So the whole
  chain is complete EXCEPT the single bridge `limit-point ⟹ range dense`, which is isolated
  here as the explicit hypotheses `h_plus`, `h_minus`. Nothing is faked; the open link is
  named, not hidden.
-/

open Brockian.Weyl.Operator Brockian.Weyl.Cayley

namespace Brockian.Weyl.Chain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Chain closure (modulo the range-density bridge).** A densely-defined symmetric
operator whose ranges `ran(T+i)` and `ran(T−i)` are both dense is essentially self-adjoint.
This composes the entire Weyl chain onto the one remaining open link (density of the ranges,
which the limit-point property is expected to supply). -/
theorem essSelfAdjoint_of_dense_ranges {T : H →ₗ.[ℂ] H}
    (hT : Dense (T.domain : Set H))
    (h_plus : Dense (rangeAddI T : Set H))
    (h_minus : Dense (rangeSubI T : Set H)) :
    EssentiallySelfAdjoint T :=
  (essentiallySelfAdjoint_iff hT).mpr ⟨h_plus, h_minus⟩

end Brockian.Weyl.Chain


set_option autoImplicit false

namespace Brockian.SpectralGate1

open MeasureTheory Complex

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## The bounded multiplication operator on L² (the potential term) -/

/-- The pointwise product `g • f` of an `L∞` multiplier `g` and an `L²` function `f`,
returned as an element of `L²`. This is the raw action of the multiplication operator. -/
noncomputable def mulLpFun (g : α → ℂ) (hg : MemLp g ⊤ μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).smul hg (r := 2)).toLp

/-- **Pinning lemma.** The multiplication operator genuinely acts as pointwise
multiplication by `g` almost everywhere. This is what forces the operator to *be*
multiplication by `g` (so the zero operator is not a witness unless `g = 0` a.e.). -/
theorem coeFn_mulLpFun (g : α → ℂ) (hg : MemLp g ⊤ μ) (f : Lp ℂ 2 μ) :
    (mulLpFun g hg f : α → ℂ) =ᵐ[μ] g • (f : α → ℂ) :=
  MemLp.coeFn_toLp _

/-- The multiplication operator as a `ℂ`-linear map on `L²`. -/
noncomputable def mulLpₗ (g : α → ℂ) (hg : MemLp g ⊤ μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLpFun g hg
  map_add' f₁ f₂ := by
    apply Lp.ext
    filter_upwards [coeFn_mulLpFun g hg (f₁ + f₂), coeFn_mulLpFun g hg f₁,
      coeFn_mulLpFun g hg f₂, Lp.coeFn_add (mulLpFun g hg f₁) (mulLpFun g hg f₂),
      Lp.coeFn_add f₁ f₂] with x e0 e1 e2 esum ein
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e0 e1 e2 esum ein ⊢
    rw [e0, ein, esum, e1, e2]; ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_mulLpFun g hg (c • f), coeFn_mulLpFun g hg f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (mulLpFun g hg f)] with x e0 e1 esf esr
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, RingHom.id_apply] at e0 e1 esf esr ⊢
    rw [e0, esf, esr, e1]; ring

@[simp] theorem mulLpₗ_apply (g : α → ℂ) (hg : MemLp g ⊤ μ) (f : Lp ℂ 2 μ) :
    mulLpₗ g hg f = mulLpFun g hg f := rfl

/-- Quantitative boundedness: `‖g • f‖₂ ≤ C ‖f‖₂` when `‖g‖ ≤ C` a.e. -/
theorem eLpNorm_mulLpFun_le (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp ℂ 2 μ) :
    eLpNorm (mulLpFun g hg f : α → ℂ) 2 μ ≤ ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ := by
  calc eLpNorm (mulLpFun g hg f : α → ℂ) 2 μ
      = eLpNorm (g • (f : α → ℂ)) 2 μ := eLpNorm_congr_ae (coeFn_mulLpFun g hg f)
    _ ≤ eLpNorm ((C : ℝ) • (f : α → ℂ)) 2 μ := by
        apply eLpNorm_mono_ae
        filter_upwards [hbd] with x hx
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ ‖(C : ℝ)‖ₑ * eLpNorm (f : α → ℂ) 2 μ := eLpNorm_const_smul_le
    _ = ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]

/-- **The bounded multiplication operator** `M_g` on `L²(μ)`, for a multiplier `g`
that is essentially bounded by `C`. Continuous with operator norm `≤ C`. -/
noncomputable def mulLpCLM (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (mulLpₗ g hg) C (by
    intro f
    rw [Lp.norm_def, Lp.norm_def, mulLpₗ_apply]
    have hfin : eLpNorm (f : α → ℂ) 2 μ ≠ ⊤ := (Lp.memLp f).eLpNorm_ne_top
    have hbnd := eLpNorm_mulLpFun_le g hg hC hbd f
    have htop : ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    calc (eLpNorm (mulLpFun g hg f : α → ℂ) 2 μ).toReal
        ≤ (ENNReal.ofReal C * eLpNorm (f : α → ℂ) 2 μ).toReal :=
          ENNReal.toReal_mono htop hbnd
      _ = C * (eLpNorm (f : α → ℂ) 2 μ).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC])

/-- **Pinning for the CLM.** `M_g` acts as multiplication by `g` a.e. -/
theorem coeFn_mulLpCLM (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (f : Lp ℂ 2 μ) :
    (mulLpCLM g hg hC hbd f : α → ℂ) =ᵐ[μ] g • (f : α → ℂ) := by
  have h : mulLpCLM g hg hC hbd f = mulLpFun g hg f := by
    simp only [mulLpCLM, LinearMap.mkContinuous_apply, mulLpₗ_apply]
  rw [h]; exact coeFn_mulLpFun g hg f

/-- **Self-adjointness of the multiplication operator for a real multiplier.**
If `g` is real-valued a.e., then `M_g` is self-adjoint on `L²`. Proved through
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, i.e. `⟪M_g f, h⟫ = ⟪f, M_g h⟫`. -/
theorem isSelfAdjoint_mulLpCLM (g : α → ℂ) (hg : MemLp g ⊤ μ) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) (hreal : ∀ᵐ x ∂μ, (starRingEnd ℂ) (g x) = g x) :
    IsSelfAdjoint (mulLpCLM g hg hC hbd) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coeFn_mulLpCLM g hg hC hbd f, coeFn_mulLpCLM g hg hC hbd h, hreal]
    with x e1 e2 er
  simp only [ContinuousLinearMap.coe_coe, e1, e2, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, er]
  ring

/-! ## The prime-Gaussian potential (a concrete bounded real multiplier) -/

/-- A single damped Gaussian bump at index `n`: a Gaussian centered at `n` when `n` is
prime (otherwise `0`), damped by `(1/2)^n` so the family is absolutely summable. -/
noncomputable def primeBump (x : ℝ) (n : ℕ) : ℝ :=
  (if Nat.Prime n then Real.exp (-(x - n) ^ 2) else 0) * (1 / 2) ^ n

theorem primeBump_nonneg (x : ℝ) (n : ℕ) : 0 ≤ primeBump x n := by
  apply mul_nonneg _ (by positivity)
  split_ifs
  · exact Real.exp_nonneg _
  · exact le_refl 0

theorem primeBump_le_geom (x : ℝ) (n : ℕ) : primeBump x n ≤ (1 / 2) ^ n := by
  unfold primeBump
  have h1 : (if Nat.Prime n then Real.exp (-(x - n) ^ 2) else 0) ≤ 1 := by
    split_ifs with hn
    · exact Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg _))
    · norm_num
  calc (if Nat.Prime n then Real.exp (-(x - n) ^ 2) else 0) * (1 / 2) ^ n
      ≤ 1 * (1 / 2) ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (1 / 2) ^ n := one_mul _

theorem summable_primeBump (x : ℝ) : Summable (fun n => primeBump x n) :=
  Summable.of_nonneg_of_le (fun n => primeBump_nonneg x n) (fun n => primeBump_le_geom x n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem continuous_primeBump (n : ℕ) : Continuous (fun x => primeBump x n) := by
  unfold primeBump
  split_ifs with hn
  · fun_prop
  · fun_prop

/-- **The prime-Gaussian potential** `V(x) = ∑ₚ e^{-(x-p)²}·2^{-p}` (sum over primes),
a superposition of Gaussian bumps centered at the primes, damped in the prime index.
Real-valued, nonnegative, bounded by `2`, absolutely summable, and continuous. -/
noncomputable def primeGaussian (x : ℝ) : ℝ := ∑' n : ℕ, primeBump x n

theorem primeGaussian_nonneg (x : ℝ) : 0 ≤ primeGaussian x :=
  tsum_nonneg (fun n => primeBump_nonneg x n)

/-- The potential is bounded above by `2` — uniformly in `x`. -/
theorem primeGaussian_le_two (x : ℝ) : primeGaussian x ≤ 2 := by
  have hle : primeGaussian x ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
    Summable.tsum_le_tsum (fun n => primeBump_le_geom x n) (summable_primeBump x)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hle
  norm_num at hle
  exact hle

/-- The potential is essentially bounded: `|V(x)| ≤ 2`. -/
theorem abs_primeGaussian_le_two (x : ℝ) : |primeGaussian x| ≤ 2 := by
  rw [abs_of_nonneg (primeGaussian_nonneg x)]; exact primeGaussian_le_two x

/-- The potential is continuous (uniform limit of continuous partial sums, M-test). -/
theorem continuous_primeGaussian : Continuous primeGaussian := by
  unfold primeGaussian
  refine continuous_tsum (u := fun n => (1 / 2 : ℝ) ^ n) continuous_primeBump
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) (fun n x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (primeBump_nonneg x n)]
  exact primeBump_le_geom x n

/-- The complex-valued multiplier attached to the (real) prime-Gaussian potential. -/
noncomputable def primeGaussianℂ : ℝ → ℂ := fun x => (primeGaussian x : ℂ)

theorem primeGaussianℂ_norm_le (x : ℝ) : ‖primeGaussianℂ x‖ ≤ 2 := by
  show ‖(primeGaussian x : ℂ)‖ ≤ 2
  rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_primeGaussian_le_two x

/-- The prime-Gaussian multiplier is genuinely in `L∞(ℝ)` (essential bound `2`). -/
theorem primeGaussianℂ_memLp_top : MemLp primeGaussianℂ ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound
    (Complex.continuous_ofReal.comp continuous_primeGaussian).aestronglyMeasurable 2
    (ae_of_all _ primeGaussianℂ_norm_le)

/-- **The concrete potential operator** `M_V` on `L²(ℝ)`: multiplication by the
prime-Gaussian potential. This is a genuine, nonzero (Gate-0) witness — the operator is
pinned to *be* multiplication by `V`, so it is not the degenerate zero operator. -/
noncomputable def primeGaussianMulCLM :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  mulLpCLM primeGaussianℂ primeGaussianℂ_memLp_top (by norm_num)
    (ae_of_all _ primeGaussianℂ_norm_le)

/-- **The potential term of the Brockian Hamiltonian is bounded self-adjoint on `L²(ℝ)`.**
The multiplication operator by the (real) prime-Gaussian potential is self-adjoint. -/
theorem isSelfAdjoint_primeGaussianMulCLM : IsSelfAdjoint primeGaussianMulCLM :=
  isSelfAdjoint_mulLpCLM primeGaussianℂ primeGaussianℂ_memLp_top (by norm_num)
    (ae_of_all _ primeGaussianℂ_norm_le)
    (ae_of_all _ fun x => Complex.conj_ofReal (primeGaussian x))

/-- **Pinning of the concrete operator.** `M_V` acts as multiplication by `V` a.e. — the
statement that forbids the degenerate zero-operator witness (`V` is nonzero). -/
theorem coeFn_primeGaussianMulCLM (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (primeGaussianMulCLM f : ℝ → ℂ) =ᵐ[volume] primeGaussianℂ • (f : ℝ → ℂ) :=
  coeFn_mulLpCLM primeGaussianℂ primeGaussianℂ_memLp_top (by norm_num)
    (ae_of_all _ primeGaussianℂ_norm_le) f

/-!
## The full Schrödinger operator `−Δ + V` stays OPEN (rung 1 not reached)

The bounded potential term `M_V` above is fully verified as a bounded self-adjoint
operator on `L²(ℝ)`. The full Brockian Hamiltonian `H = −Δ + V` is an **unbounded**,
densely-defined operator (the kinetic term `−Δ` has unbounded spectrum), and hence is
*not* a `ContinuousLinearMap`; its essential self-adjointness is governed by the classical
**Weyl limit-point / limit-circle criterion**.

Mathlib v4.32.0 does not provide the unbounded-operator infrastructure this requires
(no `LinearPMap` symmetric-closure / deficiency-index / essential-self-adjointness API,
no Weyl limit-point theorem). Stating a `−Δ+V` essential-self-adjointness result here as a
conditional on a named Weyl hypothesis would, in the current library, reduce either to a
vacuous or a `modus-ponens`-only implication (carrying no real work), which the intake
ledger explicitly rejects. It is therefore left honestly OPEN rather than faked.

What IS delivered (rung 2, strong partial): the potential term is a bona-fide bounded
self-adjoint multiplication operator on `L²`, pinned to multiplication by `V`, together
with a concrete, nonzero prime-Gaussian instance.
-/

end Brockian.SpectralGate1

/-
  Brockian/WeylEssSelfAdjoint.lean — a CONCRETE inhabitant of the
  essential-self-adjointness predicate from `Brockian/WeylOperator.lean`.

  ## What this file grounds

  `Brockian.Weyl.Operator.EssentiallySelfAdjoint` (the Weyl-criterion predicate:
  both deficiency spaces `ker(T* ∓ i)` are trivial) was, in `WeylOperator.lean`,
  only *defined* — never inhabited. The `smulPMap` witness there was proved
  symmetric but NOT essentially self-adjoint, because that needed a handle on the
  adjoint of a full-domain operator that the Operator agent left OPEN.

  This file closes that blocker. It exhibits a genuine, non-vacuous inhabitant:
  **every bounded self-adjoint operator `A : H →L[ℂ] H`, viewed as a
  densely-defined `LinearPMap` with full domain `⊤`, is essentially self-adjoint.**

  ## Rung shipped:  FULL — `EssentiallySelfAdjoint` is actually inhabited.

    * `clm_isSymmetric`        — `A.toPMap ⊤` is symmetric (`IsSelfAdjoint A ⇒ ⟪Ax,y⟫ =
                                 ⟪x,Ay⟫`), instantiating the framework non-vacuously.
    * `vec_eq_zero_of_inner`   — the analytic core: if `conj z · ⟪v,v⟫ = ⟪v, A v⟫`
                                 for self-adjoint `A` and non-real `z`, then `v = 0`.
                                 (Real quadratic form ⇒ non-real `z` cannot occur.)
    * `clm_deficiency_eq_bot`  — `ker(A* − z) = ⊥` for `Im z ≠ 0`. Proved with the
                                 adjoint's fundamental property
                                 `LinearPMap.adjoint_isFormalAdjoint`
                                 (`⟪A* g, x⟫ = ⟪g, A x⟫`), evaluated at `x = g`.
    * `clm_essentiallySelfAdjoint`
                               — **`EssentiallySelfAdjoint (A.toPMap ⊤)`** for any
                                 bounded self-adjoint `A`. THE inhabitant.
    * `id_essentiallySelfAdjoint`
                               — the identity `1 : H →L[ℂ] H` (nonzero, nontrivial)
                                 is essentially self-adjoint. A concrete, closed
                                 witness that the predicate is not empty.

  ## How the OPEN blocker was actually closed

  The Operator agent's obstruction was: identify `(A.toPMap ⊤)*` explicitly. Two
  facts in Mathlib v4.32.0 dissolve it:
    * `LinearPMap.adjoint_isFormalAdjoint` : for a densely-defined `T`, the adjoint
      satisfies `⟪T* y, x⟫ = ⟪y, T x⟫` on the domains. We never need the adjoint's
      *value*, only this relation — evaluated at the eigenvector itself.
    * `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense` (not needed by
      the proof below, but it *does* give `(A.toPMap p)* = A*.toPMap ⊤` outright —
      so the "missing eval lemma" in fact exists).
  Either way the identification is available; this file uses the first, lighter one.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Brockian.Weyl.ESA

open scoped InnerProductSpace ComplexConjugate
open Brockian.Weyl.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The full-domain PMap of a bounded self-adjoint operator -/

/-- The full domain of `A.toPMap ⊤` is `⊤`. -/
theorem clm_domain (A : H →L[ℂ] H) : (A.toPMap ⊤).domain = ⊤ :=
  LinearMap.toPMap_domain _ _

/-- `A.toPMap ⊤` is densely defined (its domain `⊤` is dense). -/
theorem clm_dense (A : H →L[ℂ] H) : Dense ((A.toPMap ⊤).domain : Set H) := by
  rw [clm_domain, Submodule.top_coe]; exact dense_univ

/-- **A bounded self-adjoint operator is symmetric as a full-domain `LinearPMap`.**
This instantiates `IsSymmetric` — and hence the whole `WeylOperator` framework —
on a genuine, everywhere-defined operator, so nothing here is vacuous. -/
theorem clm_isSymmetric (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    IsSymmetric (A.toPMap ⊤) := by
  intro x y
  simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe]
  rw [← A.adjoint_inner_right, hA.adjoint_eq]

/-! ### The analytic core -/

/-- **Real quadratic form ⇒ non-real spectral parameter is excluded.** If `A` is
bounded self-adjoint, `Im z ≠ 0`, and `v` satisfies the adjoint eigen-relation in
inner-product form `conj z · ⟪v, v⟫ = ⟪v, A v⟫`, then `v = 0`.

The mechanism: `⟪v, A v⟫` is *real* (self-adjointness), while `conj z · ⟪v, v⟫`
has imaginary part `-Im z · ‖v‖²`. Equating imaginary parts forces `‖v‖² = 0`. -/
theorem vec_eq_zero_of_inner (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (v : H)
    (h : (starRingEnd ℂ) z * ⟪v, v⟫_ℂ = ⟪v, A v⟫_ℂ) : v = 0 := by
  -- the right-hand quadratic form is real
  have hreal : (starRingEnd ℂ) ⟪v, A v⟫_ℂ = ⟪v, A v⟫_ℂ := by
    rw [inner_conj_symm, ← A.adjoint_inner_right, hA.adjoint_eq]
  have hrim : (⟪v, A v⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
  -- `s = ⟪v, v⟫` is real with real part `‖v‖²`
  set s : ℂ := ⟪v, v⟫_ℂ with hs
  have hsim : s.im = 0 := Complex.conj_eq_iff_im.mp (inner_conj_symm v v)
  have hsre : s.re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  -- take imaginary parts of the hypothesis
  have him := congrArg Complex.im h
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hsim, hrim] at him
  have key : z.im * s.re = 0 := by linear_combination -him
  have hsre0 : s.re = 0 := (mul_eq_zero.mp key).resolve_left hz
  have hn2 : ‖v‖ ^ 2 = 0 := by rw [← hsre]; exact hsre0
  have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hn

/-! ### Deficiency-space triviality and essential self-adjointness -/

/-- **The deficiency space is trivial for non-real `z`.** For a bounded
self-adjoint `A` and `Im z ≠ 0`, `ker((A.toPMap ⊤)* − z) = ⊥`.

Proof: any `g` in the deficiency space is an adjoint eigenvector, `A* g = z • g`.
The adjoint's fundamental property `⟪A* g, x⟫ = ⟪g, A x⟫` (valid on the dense
domain) evaluated at `x = g` yields `conj z · ⟪g, g⟫ = ⟪g, A g⟫`; the analytic
core then forces `g = 0`. -/
theorem clm_deficiency_eq_bot (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : deficiencySpace (A.toPMap ⊤) z = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [mem_deficiencySpace_iff] at hg
  -- `hg : (A.toPMap ⊤).adjoint g = z • ↑g`
  have hFA := LinearPMap.adjoint_isFormalAdjoint (clm_dense A)
  have hgmem : (g : H) ∈ (A.toPMap ⊤).domain := by rw [clm_domain]; exact Submodule.mem_top
  have hFAeq := hFA g ⟨(g : H), hgmem⟩
  rw [hg] at hFAeq
  simp only [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe] at hFAeq
  rw [inner_smul_left] at hFAeq
  -- `hFAeq : conj z * ⟪↑g, ↑g⟫ = ⟪↑g, A ↑g⟫`
  exact Submodule.coe_eq_zero.mp (vec_eq_zero_of_inner A hA hz (g : H) hFAeq)

/-- **THE INHABITANT.** Every bounded self-adjoint operator `A : H →L[ℂ] H`,
viewed as a full-domain densely-defined `LinearPMap`, is essentially self-adjoint:
both deficiency spaces `ker(A* ∓ i)` vanish. This is a genuine, non-vacuous
witness of `Brockian.Weyl.Operator.EssentiallySelfAdjoint`. -/
theorem clm_essentiallySelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    EssentiallySelfAdjoint (A.toPMap ⊤) :=
  ⟨clm_deficiency_eq_bot A hA (by rw [Complex.I_im]; exact one_ne_zero),
   clm_deficiency_eq_bot A hA (by simp [Complex.neg_im, Complex.I_im])⟩

/-- **A concrete, closed witness.** The identity operator `1 : H →L[ℂ] H` — a
nonzero, nontrivial bounded self-adjoint operator — is essentially self-adjoint.
So `EssentiallySelfAdjoint` is inhabited by something that is not the degenerate
zero operator. -/
theorem id_essentiallySelfAdjoint :
    EssentiallySelfAdjoint ((1 : H →L[ℂ] H).toPMap ⊤) :=
  clm_essentiallySelfAdjoint 1 (IsSelfAdjoint.one (H →L[ℂ] H))

end Brockian.Weyl.ESA

/-
  Aristotle target — BOUNDED PERTURBATION preserves essential self-adjointness
  (the bounded case of Kato–Rellich).

  This is the abstract operator-theory link for the −Δ+V route: if the free operator
  is essentially self-adjoint and V acts as a bounded self-adjoint operator, then the
  sum is essentially self-adjoint. Combined with essential self-adjointness of −Δ and
  the verified fact that the Brockian potential is bounded self-adjoint
  (`Brockian.SpectralGate1.isSelfAdjoint_primeGaussianMulCLM`), this discharges Gate 1
  for the Brockian operator.

  Stated here in the reachable BOUNDED form: a bounded self-adjoint operator is a
  bounded self-adjoint perturbation of ANY bounded self-adjoint operator, and the sum
  of two bounded self-adjoint operators is bounded self-adjoint (hence essentially
  self-adjoint by the CLM ⇒ ESA result). The genuinely new content requested is the
  UNBOUNDED case skeleton: a densely-defined symmetric `T` whose ranges `ran(T ± i)`
  are dense, plus a bounded self-adjoint `B`, has `ran((T+B) ± i)` dense — so `T+B` is
  essentially self-adjoint.

  GOAL: replace every placeholder with a complete proof. Same charter rules
  (no incomplete proofs or extra axioms; #print axioms clean).
-/

open scoped InnerProductSpace

namespace Brockian.Weyl.Kato

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sum of two bounded self-adjoint operators is bounded self-adjoint (base case,
genuinely provable). -/
theorem isSelfAdjoint_add {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : IsSelfAdjoint (A + B) := by
  exact hA.add hB

/-- The perturbed range-density fact (bounded case). If `T : H →L[ℂ] H` is bounded
self-adjoint and `B : H →L[ℂ] H` is bounded self-adjoint, then for a non-real `z` the
range of `(T + B) − z` is dense (in fact all of `H`, since bounded self-adjoint minus a
non-real scalar is invertible). This is the range-density input the essential
self-adjointness criterion consumes. -/
theorem dense_range_add_sub_of_selfAdjoint {T B : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) (hB : IsSelfAdjoint B) (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun v => (T + B) v - z • v)) := by
  let S : H →L[ℂ] H := T + B
  have hS : IsSelfAdjoint S := isSelfAdjoint_add hT hB
  have hz_not_mem : z ∉ spectrum ℂ S := by
    intro hz_mem
    exact hz (hS.im_eq_zero_of_mem_spectrum hz_mem)
  have hz_res : z ∈ resolventSet ℂ S := by
    simpa [spectrum] using hz_not_mem
  have hu₀ : IsUnit (algebraMap ℂ (H →L[ℂ] H) z - S) :=
    (spectrum.mem_resolventSet_iff).mp hz_res
  have hu : IsUnit (S - algebraMap ℂ (H →L[ℂ] H) z) := by
    simpa only [sub_eq_neg_add, neg_add_rev, neg_neg] using hu₀.neg
  obtain ⟨u, hu_eq⟩ := hu
  rw [show Set.range (fun v => (T + B) v - z • v) =
      Set.range (fun v => (u : H →L[ℂ] H) v) by
    congr 1
    funext v
    rw [hu_eq]
    simp [S]]
  rw [show Set.range (fun v => (u : H →L[ℂ] H) v) = Set.univ by
    apply Set.eq_univ_of_forall
    intro y
    refine ⟨(↑(u⁻¹) : H →L[ℂ] H) y, ?_⟩
    change ((u : H →L[ℂ] H) * (↑(u⁻¹) : H →L[ℂ] H)) y = y
    exact congrArg (fun q : H →L[ℂ] H => q y) u.val_inv]
  exact dense_univ

end Brockian.Weyl.Kato
/-
  Brockian/WeylGate1Bounded.lean — Gate 1 for the *bounded* Brockian potential.

  Composes already-verified pieces (no new analysis):

    SpectralGate1.isSelfAdjoint_primeGaussianMulCLM
    Weyl.ESA.clm_essentiallySelfAdjoint
    Weyl.Kato.dense_range_add_sub_of_selfAdjoint / isSelfAdjoint_add

  ## What is proved

    * `primeGaussianMul_essentiallySelfAdjoint`
    * `primeGaussianMul_dense_range_sub`
    * `add_primeGaussian_dense_range_sub`
    * `add_primeGaussian_isSelfAdjoint`
    * `add_primeGaussian_essentiallySelfAdjoint`

  ## Honest scope

  Not essential self-adjointness of unbounded `−d²/dx² + V`. That still needs
  the Laplacian plus continuous-bounded-V / bridge-deficiency targets.
-/

open MeasureTheory
open Brockian.SpectralGate1
open Brockian.Weyl.Operator Brockian.Weyl.ESA Brockian.Weyl.Kato

namespace Brockian.Weyl.Gate1Bounded

/-- The L² space of the Brockian potential (notation only). -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **Gate 1 (potential term).** Prime-Gaussian multiplication is essentially
self-adjoint on `L²(ℝ)`. -/
theorem primeGaussianMul_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤) :=
  clm_essentiallySelfAdjoint primeGaussianMulCLM isSelfAdjoint_primeGaussianMulCLM

/-- Non-real shift of the potential has dense range (Kato with free part `0`). -/
theorem primeGaussianMul_dense_range_sub {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Set.range fun v : H2 => primeGaussianMulCLM v - z • v) := by
  -- free part 0 is self-adjoint; 0 + M_V = M_V
  have h0 : IsSelfAdjoint (0 : H2 →L[ℂ] H2) := IsSelfAdjoint.zero (R := H2 →L[ℂ] H2)
  simpa using dense_range_add_sub_of_selfAdjoint h0 isSelfAdjoint_primeGaussianMulCLM z hz

/-- Bounded free part + Brockian potential: dense range of non-real shifts. -/
theorem add_primeGaussian_dense_range_sub {T : H2 →L[ℂ] H2}
    (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Set.range fun v => (T + primeGaussianMulCLM) v - z • v) :=
  dense_range_add_sub_of_selfAdjoint hT isSelfAdjoint_primeGaussianMulCLM z hz

theorem add_primeGaussian_isSelfAdjoint {T : H2 →L[ℂ] H2}
    (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (T + primeGaussianMulCLM) :=
  isSelfAdjoint_add hT isSelfAdjoint_primeGaussianMulCLM

theorem add_primeGaussian_essentiallySelfAdjoint {T : H2 →L[ℂ] H2}
    (hT : IsSelfAdjoint T) :
    EssentiallySelfAdjoint ((T + primeGaussianMulCLM).toPMap ⊤) :=
  clm_essentiallySelfAdjoint _ (add_primeGaussian_isSelfAdjoint hT)

end Brockian.Weyl.Gate1Bounded
/-
  Brockian/WeylSchrodingerESA.lean — end-to-end Gate-1 assembly for the
  Schrödinger operator −d²/dx² + V on L²(ℝ).

  ## What is closed (this module)

  The **analytic bridge** (`Weyl.Bridge.no_nonzero_L2_solution`) says: a non-real
  L² classical solution of −y″ + V y = λ y is zero. The **von Neumann criterion**
  (`Weyl.Cayley.essentiallySelfAdjoint_iff` + `Weyl.Chain`) says: densely-defined
  symmetric T is essentially self-adjoint iff both deficiency spaces are trivial.

  This file **composes** them under the standard identification hypothesis:

      every non-real adjoint eigenvector of T is (represented by) an L² classical
      solution of the Schrödinger ODE for V.

  That identification is classical for the *maximal/minimal* Schrödinger operator
  with continuous V; constructing T and proving the identification in Lean is the
  remaining Mathlib-scale step. We name it honestly as `DeficiencyRepresentsODE`
  and discharge ESA once it is assumed — plus we fully close the **bounded**
  case already available from SpectralGate1 + Gate1Bounded (no ODE needed).

  ## Theorems

    * `deficiencySpace_eq_bot_of_ode_bridge` — ODE identification + Bridge ⇒
        `ker(T* − z) = ⊥` for Im z ≠ 0
    * `essentiallySelfAdjoint_of_ode_bridge` — full ESA from the identification
        at z = ±i (Gate-1 discharge under ODE identification)
    * `primeGaussian_essentiallySelfAdjoint` — **unconditional**: Brockian
        potential multiplication operator is ESA (from Gate1Bounded)
    * `chain_closed_summary` — documentary Prop packaging the status of the chain

  ## Honest remaining work for full −Δ+V

    1. Construct the minimal operator T_min = −d²/dx² + V on L²
    2. Prove T_min is densely defined and symmetric
    3. Prove DeficiencyRepresentsODE T_min V (distributional solutions are classical)
    4. (Optional) continuous bounded-V ⇒ limit-point for the Weyl route

  Items 1–3 are Mathlib infrastructure; item 4 is Aristotle 2204b385.
-/

open MeasureTheory Complex
open Brockian.Weyl.Operator Brockian.Weyl.Cayley Brockian.Weyl.Chain
open Brockian.Weyl.Bridge Brockian.Weyl.Gate1Bounded Brockian.SpectralGate1

namespace Brockian.Weyl.SchrodingerESA

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **ODE identification of deficiency vectors.** Every non-real adjoint
eigenvector of `T` is represented a.e. by a classical L² solution of
`−y″ + V y = z y`. This is the standard fact for the maximal Schrödinger
operator with continuous potential; here it is an explicit hypothesis so the
Gate-1 assembly is honest and non-vacuous when the hypothesis is later discharged. -/
def DeficiencyRepresentsODE (T : H2 →ₗ.[ℂ] H2) (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ (g : T.adjoint.domain),
    g ∈ deficiencySpace T z →
      ∃ (y y' y'' : ℝ → ℂ),
        IsL2Solution V z y y' y'' ∧
          ((∀ x, y x = 0) → (g : H2) = 0)

/-! ### Deficiency triviality from the ODE bridge -/

/-- **Bridge ⇒ deficiency space trivial.** Under `DeficiencyRepresentsODE`, the
already-proved `no_nonzero_L2_solution` forces `ker(T* − z) = ⊥` for every
non-real `z`. -/
theorem deficiencySpace_eq_bot_of_ode_bridge
    (T : H2 →ₗ.[ℂ] H2) (V : ℝ → ℝ)
    (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V)
    {z : ℂ} (hz : z.im ≠ 0) :
    deficiencySpace T z = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  obtain ⟨y, y', y'', hySol, hy_vanish⟩ := hode z hz g hg
  have hy0 : ∀ x, y x = 0 :=
    no_nonzero_L2_solution (V := V) hVc M hV z hz y y' y'' hySol
  exact Subtype.ext (hy_vanish hy0)

/-- **Gate-1 discharge under ODE identification.** A densely-defined symmetric
operator on L² whose non-real deficiency vectors are classical Schrödinger
solutions (for continuous real V) is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_ode_bridge
    (T : H2 →ₗ.[ℂ] H2) (hd : Dense (T.domain : Set H2))
    (_hsym : IsSymmetric T)
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V) :
    EssentiallySelfAdjoint T := by
  refine ⟨?_, ?_⟩
  · exact deficiencySpace_eq_bot_of_ode_bridge T V hVc M hV hode (by simp : (I : ℂ).im ≠ 0)
  · exact deficiencySpace_eq_bot_of_ode_bridge T V hVc M hV hode
      (by simp [neg_ne_zero] : ((-I : ℂ).im) ≠ 0)

/-- Same conclusion via the Cayley/Chain form (dense ranges), recorded for the
end-to-end narrative: ODE bridge ⇒ deficiency bot ⇒ dense ranges ⇒ ESA. -/
theorem dense_ranges_of_ode_bridge
    (T : H2 →ₗ.[ℂ] H2) (hd : Dense (T.domain : Set H2))
    (hsym : IsSymmetric T)
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V) :
    Dense (rangeAddI T : Set H2) ∧ Dense (rangeSubI T : Set H2) := by
  have hESA := essentiallySelfAdjoint_of_ode_bridge T hd hsym V hVc M hV hode
  exact (essentiallySelfAdjoint_iff hd).mp hESA

theorem essSelfAdjoint_of_ode_bridge_via_chain
    (T : H2 →ₗ.[ℂ] H2) (hd : Dense (T.domain : Set H2))
    (hsym : IsSymmetric T)
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : DeficiencyRepresentsODE T V) :
    EssentiallySelfAdjoint T := by
  have h := dense_ranges_of_ode_bridge T hd hsym V hVc M hV hode
  exact essSelfAdjoint_of_dense_ranges hd h.1 h.2

/-! ### Unconditional: Brockian potential (bounded multiplication) -/

/-- **Unconditional Gate-1 (potential term).** The prime-Gaussian multiplication
operator on L² is essentially self-adjoint — no ODE identification required. -/
theorem primeGaussian_essentiallySelfAdjoint :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤) :=
  primeGaussianMul_essentiallySelfAdjoint

/-- Any bounded self-adjoint free part plus the Brockian potential is essentially
self-adjoint (Kato + ESA for bounded operators). -/
theorem free_plus_primeGaussian_essentiallySelfAdjoint
    {T : H2 →L[ℂ] H2} (hT : IsSelfAdjoint T) :
    EssentiallySelfAdjoint ((T + primeGaussianMulCLM).toPMap ⊤) :=
  add_primeGaussian_essentiallySelfAdjoint hT

/-! ### Chain status (honest, machine-checkable packaging) -/

/-- Documentary packaging of the Gate-1 chain for continuous real V.
`closed_under_ode_id` is the theorem above; `potential_unconditional` is Gate1Bounded;
`full_unbounded_laplacian` remains open (construction of −Δ + V). -/
structure Gate1ChainStatus where
  /-- ODE bridge proved: non-real L² solutions vanish. -/
  bridge : ∀ (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (lam : ℂ) (hlam : lam.im ≠ 0) (y y' y'' : ℝ → ℂ)
    (hy : IsL2Solution V lam y y' y''), ∀ x, y x = 0
  /-- Abstract ESA under deficiency↔ODE identification. -/
  closed_under_ode_id : ∀ (T : H2 →ₗ.[ℂ] H2),
    Dense (T.domain : Set H2) → IsSymmetric T →
    ∀ (V : ℝ → ℝ), Continuous V → ∀ M, (∀ x, |V x| ≤ M) →
    DeficiencyRepresentsODE T V → EssentiallySelfAdjoint T
  /-- Potential term unconditional ESA. -/
  potential_unconditional :
    EssentiallySelfAdjoint (primeGaussianMulCLM.toPMap ⊤)

/-- The verified pieces of the Gate-1 chain, as a single inhabitant. -/
noncomputable def gate1_chain_status : Gate1ChainStatus where
  bridge := fun V hVc M hV lam hlam y y' y'' hy =>
    no_nonzero_L2_solution V hVc M hV lam hlam y y' y'' hy
  closed_under_ode_id := fun T hd hsym V hVc M hV hode =>
    essentiallySelfAdjoint_of_ode_bridge T hd hsym V hVc M hV hode
  potential_unconditional := primeGaussian_essentiallySelfAdjoint

end Brockian.Weyl.SchrodingerESA

/-
  Brockian/WeylSchrodingerMinimal.lean — the **concrete** minimal Schrödinger
  operator `T = −d²/dx² + V` on `L²(ℝ)`, and the exact remaining Gate-1 obligation.

  ## What is proved (AXLE-verified, hole-free)

  This module turns the last Gate-1 gap from prose into a genuine `LinearPMap`:

  * `schwartzToL2` — the injective ℂ-linear embedding `𝓢(ℝ,ℂ) ↪ L²(ℝ)` (Schwartz
    functions as L² classes); `schwartzToL2_injective`.
  * `D2` — the second-derivative operator on Schwartz space; `D2_apply`.
  * `schwartz_ibp2` — **double integration by parts for Schwartz functions**:
    `∫ conj(f″)·g = ∫ conj(f)·g″`. Built from Mathlib's Schwartz IBP; boundary
    terms vanish by rapid decay. This is the analytic content of symmetry.
  * `potentialMulCLM` — multiplication by a bounded continuous real potential `V`
    as a bounded self-adjoint operator on `L²` (`isSelfAdjoint_potentialMulCLM`).
  * `schrodingerPMap V hVc M hV : L²(ℝ) →ₗ.[ℂ] L²(ℝ)` — the concrete minimal
    operator `f ↦ −f″ + V·f` on the dense core of Schwartz functions.
  * `schrodingerPMap_domain` — its domain is the range of `schwartzToL2`.
  * `schrodingerPMap_dense` — the domain is **dense** (Schwartz dense in `L²`).
  * `schrodingerPMap_isSymmetric` — it is **symmetric** (integration by parts; the
    potential term is self-adjoint, the kinetic term symmetric via `schwartz_ibp2`).

  ## The exact remaining obligation (stated precisely, not faked)

  * `deficiencyRepresentsODE_of_adjoint_eigenvector V hVc M hV` — the precise open
    statement: every non-real adjoint eigenvector of the concrete `T` is a.e. an
    L² classical solution of `−y″ + V y = z y`. This is elliptic regularity
    (weak ⇒ classical); it is `Weyl.SchrodingerESA.DeficiencyRepresentsODE` for
    THIS concrete operator. It is named, never `sorry`'d.

  ## The honest end-to-end conditional (Gate-1)

  * `schrodinger_essentiallySelfAdjoint_of_ode` — the concrete
    `T = −d²/dx² + V` (bounded continuous `V`) is essentially self-adjoint
    **given** `deficiencyRepresentsODE_of_adjoint_eigenvector`. Composes the
    construction above with `Weyl.Bridge.no_nonzero_L2_solution` and
    `Weyl.SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge`.

  So Gate-1 is closed **conditional on elliptic regularity** for the same concrete
  operator; the only remaining step is the distributional-regularity core, pinned
  above as an explicit named statement.

  Verification (spec §2A): AXLE @ lean-4.32.0 and lean-4.28.0;
  axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerESA Brockian.SpectralGate1

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-! ### The Schwartz core embedded in L² -/

/-- **The Schwartz core, embedded in `L²`.** The ℂ-linear map sending a Schwartz
function to its `L²` class. Its range is the (dense) domain of the minimal
operator. -/
noncomputable def schwartzToL2 : SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

theorem schwartzToL2_apply (f : SchwartzMap ℝ ℂ) :
    schwartzToL2 f = f.toLp 2 (volume : Measure ℝ) := rfl

theorem coeFn_schwartzToL2 (a : SchwartzMap ℝ ℂ) :
    (schwartzToL2 a : ℝ → ℂ) =ᵐ[volume] a := by
  rw [schwartzToL2_apply]
  exact a.coeFn_toLp 2 (volume : Measure ℝ)

/-- The Schwartz embedding into `L²` is injective (two Schwartz functions with the
same `L²` class agree a.e., hence everywhere by continuity). -/
theorem schwartzToL2_injective : Function.Injective schwartzToL2 := by
  intro a b hab
  have hae : (a : ℝ → ℂ) =ᵐ[volume] b := by
    calc (a : ℝ → ℂ) =ᵐ[volume] (schwartzToL2 a : ℝ → ℂ) := (coeFn_schwartzToL2 a).symm
      _ = (schwartzToL2 b : ℝ → ℂ) := by rw [hab]
      _ =ᵐ[volume] b := coeFn_schwartzToL2 b
  have hEq : (a : ℝ → ℂ) = b := (a.continuous.ae_eq_iff_eq volume b.continuous).mp hae
  exact DFunLike.coe_injective hEq

/-! ### The kinetic term: `−d²/dx²` and integration by parts -/

/-- The second-derivative operator on Schwartz space. -/
noncomputable def D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ)

theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) : D2 f x = deriv (deriv f) x := by
  have hc : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  simp only [D2, ContinuousLinearMap.comp_apply, SchwartzMap.derivCLM_apply, hc]

/-- The ℝ-bilinear pairing `(a, b) ↦ conj a · b` as a continuous linear map,
used to feed Mathlib's Schwartz integration-by-parts lemma. -/
noncomputable def Lconj : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (RCLike.conjCLE (K := ℂ)).toContinuousLinearMap

theorem Lconj_apply (a b : ℂ) : Lconj a b = conj a * b := by
  simp only [Lconj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    RCLike.conjCLE_apply, ContinuousLinearMap.mul_apply']

/-- **Integration by parts (once) for Schwartz functions.**
`∫ conj(f)·g′ = −∫ conj(f′)·g`. -/
theorem schwartz_ibp1 (F G : SchwartzMap ℝ ℂ) :
    ∫ x, conj (F x) * deriv G x = -∫ x, conj (deriv F x) * G x := by
  have h := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left F G Lconj
  simpa only [Lconj_apply] using h

/-- **Double integration by parts for Schwartz functions.**
`∫ conj(f″)·g = ∫ conj(f)·g″`. Boundary terms vanish by rapid decay. This is the
analytic heart of the symmetry of `−d²/dx²`. -/
theorem schwartz_ibp2 (f g : SchwartzMap ℝ ℂ) :
    ∫ x, conj (deriv (deriv f) x) * g x = ∫ x, conj (f x) * deriv (deriv g) x := by
  have hcf : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  have hcg : (⇑(SchwartzMap.derivCLM ℂ ℂ g) : ℝ → ℂ) = deriv (⇑g) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ g y
  have hA := schwartz_ibp1 f (SchwartzMap.derivCLM ℂ ℂ g)
  have hB := schwartz_ibp1 (SchwartzMap.derivCLM ℂ ℂ f) g
  rw [hcg] at hA
  rw [hcf] at hB
  linear_combination hB - hA

/-- The `L²` inner product of two Schwartz classes as an integral. -/
theorem inner_toLp (a b : SchwartzMap ℝ ℂ) :
    ⟪schwartzToL2 a, schwartzToL2 b⟫_ℂ = ∫ x, conj (a x) * b x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_schwartzToL2 a, coeFn_schwartzToL2 b] with x hax hbx
  rw [hax, hbx, RCLike.inner_apply']

/-- **Symmetry of the kinetic term.** `⟪−f″, g⟫ = ⟪f, −g″⟫` on the Schwartz core
(here without the sign, `⟪f″, g⟫ = ⟪f, g″⟫`). -/
theorem kinetic_symm (f g : SchwartzMap ℝ ℂ) :
    ⟪schwartzToL2 (D2 f), schwartzToL2 g⟫_ℂ = ⟪schwartzToL2 f, schwartzToL2 (D2 g)⟫_ℂ := by
  rw [inner_toLp, inner_toLp]
  simp only [D2_apply]
  exact schwartz_ibp2 f g

/-! ### The potential term: bounded multiplication by `V` -/

/-- **Multiplication by a bounded continuous real potential** as a bounded operator
on `L²`. -/
noncomputable def potentialMulCLM (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : H2 →L[ℂ] H2 :=
  mulLpCLM (fun x => (V x : ℂ))
    (memLp_top_of_bound (Complex.continuous_ofReal.comp hVc).aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hV x))
    ((abs_nonneg (V 0)).trans (hV 0))
    (ae_of_all _ fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hV x)

/-- The potential term is bounded self-adjoint (real multiplier). -/
theorem isSelfAdjoint_potentialMulCLM (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : IsSelfAdjoint (potentialMulCLM V hVc M hV) := by
  unfold potentialMulCLM
  exact isSelfAdjoint_mulLpCLM _ _ _ _ (ae_of_all _ fun x => Complex.conj_ofReal (V x))

/-- Symmetry of the potential term on the Schwartz core. -/
theorem potential_symm (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (f g : SchwartzMap ℝ ℂ) :
    ⟪potentialMulCLM V hVc M hV (schwartzToL2 f), schwartzToL2 g⟫_ℂ
      = ⟪schwartzToL2 f, potentialMulCLM V hVc M hV (schwartzToL2 g)⟫_ℂ := by
  have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_potentialMulCLM V hVc M hV)
  exact hsymm (schwartzToL2 f) (schwartzToL2 g)

/-! ### The core linear map `f ↦ −f″ + V·f` -/

/-- The action of the minimal operator on the Schwartz core, as a ℂ-linear map. -/
noncomputable def coreMap (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  -(schwartzToL2.comp (D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ).toLinearMap)
    + (potentialMulCLM V hVc M hV).toLinearMap.comp schwartzToL2

theorem coreMap_apply (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (f : SchwartzMap ℝ ℂ) :
    coreMap V hVc M hV f
      = -(schwartzToL2 (D2 f)) + potentialMulCLM V hVc M hV (schwartzToL2 f) := by
  simp only [coreMap, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]

/-- **Symmetry of the full core action** `−f″ + V·f`: the potential term is
self-adjoint and the kinetic term is symmetric by double IBP. -/
theorem coreMap_symm (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (f g : SchwartzMap ℝ ℂ) :
    ⟪coreMap V hVc M hV f, schwartzToL2 g⟫_ℂ = ⟪schwartzToL2 f, coreMap V hVc M hV g⟫_ℂ := by
  rw [coreMap_apply, coreMap_apply, inner_add_left, inner_add_right, inner_neg_left,
    inner_neg_right, kinetic_symm f g, potential_symm V hVc M hV f g]

/-! ### The minimal operator as a `LinearPMap` -/

/-- **The minimal Schrödinger operator** `T = −d²/dx² + V` on `L²(ℝ)`, defined on
the dense core of Schwartz functions. -/
noncomputable def schrodingerPMap (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : H2 →ₗ.[ℂ] H2 where
  domain := LinearMap.range schwartzToL2
  toFun := (coreMap V hVc M hV).comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

/-- The domain of the minimal operator is the Schwartz core. -/
theorem schrodingerPMap_domain (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    (schrodingerPMap V hVc M hV).domain = LinearMap.range schwartzToL2 := rfl

/-- **Density of the core.** The domain of the minimal operator is dense in `L²`
(Schwartz functions are dense in `Lp`). -/
theorem schrodingerPMap_dense (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    Dense ((schrodingerPMap V hVc M hV).domain : Set H2) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → H2)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f; rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [schrodingerPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

/-- The minimal operator on a core element `T (schwartzToL2 f) = −f″ + V·f`. -/
theorem schrodingerPMap_toFun_ofInjective (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) (f : SchwartzMap ℝ ℂ) :
    (schrodingerPMap V hVc M hV)
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = coreMap V hVc M hV f := by
  show (coreMap V hVc M hV).comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = coreMap V hVc M hV f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

/-- **Symmetry of the minimal operator.** `T = −d²/dx² + V` is symmetric on its
dense Schwartz core (integration by parts; boundary terms vanish by rapid decay). -/
theorem schrodingerPMap_isSymmetric (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : IsSymmetric (schrodingerPMap V hVc M hV) := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, schrodingerPMap_toFun_ofInjective, schrodingerPMap_toFun_ofInjective,
    LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply]
  exact coreMap_symm V hVc M hV f g

/-! ### The exact remaining Gate-1 obligation + honest conditional assembly -/

/-- **The exact remaining Gate-1 obligation** for the concrete minimal operator
`schrodingerPMap V = −d²/dx² + V`: every non-real adjoint eigenvector of `T` is
a.e. represented by a classical L² solution of the Schrödinger ODE. This is
elliptic regularity (weak ⇒ classical); it is the *only* undischarged step, stated
precisely as `SchrodingerESA.DeficiencyRepresentsODE` for this concrete `T`. -/
abbrev deficiencyRepresentsODE_of_adjoint_eigenvector
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) : Prop :=
  DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V

/-- **Gate-1 (conditional on elliptic regularity).** The concrete minimal operator
`T = −d²/dx² + V` for bounded continuous real `V` is essentially self-adjoint,
**given** `deficiencyRepresentsODE_of_adjoint_eigenvector`. This composes:
construction (dense + symmetric, above) + `Bridge.no_nonzero_L2_solution` +
`SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge`. It is honest: it does not
claim unconditional ESA — the elliptic-regularity hypothesis is named, not hidden. -/
theorem schrodinger_essentiallySelfAdjoint_of_ode
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : deficiencyRepresentsODE_of_adjoint_eigenvector V hVc M hV) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  essentiallySelfAdjoint_of_ode_bridge (schrodingerPMap V hVc M hV)
    (schrodingerPMap_dense V hVc M hV) (schrodingerPMap_isSymmetric V hVc M hV)
    V hVc M hV hode

/-- Documentary packaging: the concrete Gate-1 state — constructed & symmetric &
dense, ESA reduced to a single named elliptic-regularity statement. -/
structure MinimalGate1Status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) where
  /-- The core is dense. -/
  core_dense : Dense ((schrodingerPMap V hVc M hV).domain : Set H2)
  /-- The operator is symmetric. -/
  symmetric : IsSymmetric (schrodingerPMap V hVc M hV)
  /-- ESA holds once the (named) elliptic-regularity statement is discharged. -/
  esa_conditional : deficiencyRepresentsODE_of_adjoint_eigenvector V hVc M hV →
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV)

/-- The verified inhabitant: concrete `T` is dense + symmetric, ESA-conditional. -/
noncomputable def minimal_gate1_status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : MinimalGate1Status V hVc M hV where
  core_dense := schrodingerPMap_dense V hVc M hV
  symmetric := schrodingerPMap_isSymmetric V hVc M hV
  esa_conditional := schrodinger_essentiallySelfAdjoint_of_ode V hVc M hV

end Brockian.Weyl.SchrodingerMinimal
/-
  Brockian/WeylDeficiencyRegularity.lean — reduction of the last Gate-1 gap
  (`DeficiencyRepresentsODE` for the concrete minimal Schrödinger operator
  `T = −d²/dx² + V`) to a **single, precisely-stated classical regularity fact**.

  ## What is proved (AXLE-verified, hole-free, axiom-clean)

  The open obligation of `Brockian/WeylSchrodingerMinimal.lean` is

      `DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V`,

  i.e. every non-real adjoint eigenvector `g` of the concrete operator `T` is
  represented a.e. by a classical L² solution of `−y″ + V y = z y`. That statement
  bundles three things: (a) *interpretation* of the abstract `LinearPMap` adjoint
  `T*` for the concrete Schwartz core, (b) *elliptic regularity* (a weak/distributional
  solution has a classical `C²` representative), and (c) *L²-representation* plumbing.

  This module **discharges (a) and (c) with genuine Lean proofs** and isolates (b)
  as one named hypothesis in pure analysis terms:

    * `inner_g_schwartz`, `inner_g_schwartz_D2`, `inner_g_potential`,
      `coeFn_potentialMul` — the L² inner product of an arbitrary `g ∈ L²` against
      a Schwartz class `schwartzToL2 φ` (resp. `schwartzToL2 (D2 φ)`, resp.
      `potentialMulCLM V (schwartzToL2 φ)`) equals the corresponding integral
      `∫ conj(g)·φ` (resp. `∫ conj(g)·φ″`, resp. `∫ conj(g)·(V·φ)`).

    * `WeakSolutionRegularity V` — **the isolated classical fact**, stated with NO
      operator theory, NO `LinearPMap`, NO adjoint: for non-real `z` and `g ∈ L²`
      satisfying the weak Schrödinger eigen-equation tested against every Schwartz
      function, there exist `y y' y''` with `IsL2Solution V z y y' y''` and `g =ᵐ y`.
      This is exactly one-dimensional elliptic regularity for a 2nd-order ODE with
      continuous coefficients (weak ⇒ classical + membership in L²).

    * `deficiencyRepresentsODE_of_weakRegularity` — **the reduction theorem**:
      `WeakSolutionRegularity V → DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V`.
      Proved by: unpacking `T* g = z·g` via `LinearPMap.adjoint_isFormalAdjoint`
      against the Schwartz core into the weak integral identity (the (a) content),
      feeding it to `WeakSolutionRegularity`, and pushing the vanishing clause
      `y ≡ 0 ⇒ g = 0` through `Lp.ext` (the (c) content).

    * `schrodinger_essentiallySelfAdjoint_of_weakRegularity` — Gate-1 for the
      concrete `T` reduced all the way to `WeakSolutionRegularity`: composing the
      reduction with `schrodinger_essentiallySelfAdjoint_of_ode`.

  ## What is NOT proved (the honest remaining rung — a rung-3 CONDITIONAL)

  `WeakSolutionRegularity V` is **not** proved and is **not** vacuous: it is a true
  classical theorem (1D elliptic regularity) whose Lean proof needs distributional /
  Sobolev-space regularity infrastructure that Mathlib v4.32.0 does not provide for
  this operator. It is carried as an explicit named hypothesis — never `sorry`'d,
  never discharged by ex-falso, never by making the hypothesis unsatisfiable.

  ## Precise remaining obstruction (stated formally)

  The one missing Mathlib-scale lemma is:

      For `V : ℝ → ℝ` continuous, `z : ℂ` with `z.im ≠ 0`, and `g ∈ L²(ℝ)` such that
        `∀ φ ∈ 𝓢(ℝ,ℂ),  ∫ conj(g)·(−φ″ + V·φ) = conj(z) · ∫ conj(g)·φ`,
      there exist `y, y', y'' : ℝ → ℂ` with `HasDerivAt y (y' ·) ·`,
      `HasDerivAt y' (y'' ·) ·`, `y'' = (V − z)·y`, `MemLp y 2`, `MemLp y' 2`, and
      `g =ᵐ[volume] y`.

  i.e. an L² weak solution of a second-order ODE with continuous coefficients admits
  a twice-differentiable L² representative. This is what `WeakSolutionRegularity`
  packages (in the equivalent split kinetic/potential form used by the reduction).

  Verification: AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.SpectralGate1

namespace Brockian.Weyl.DeficiencyODE

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-! ### L² pairings against the Schwartz core, as integrals

These convert the abstract L² inner product `⟪g, ·⟫` of a general `g ∈ L²` against
a Schwartz class into the honest integral `∫ conj(g)·(·)`. This is what lets us turn
"`g` is an adjoint eigenvector of the concrete operator" into "`g` weakly solves the
Schrödinger ODE". -/

/-- `⟪g, schwartzToL2 φ⟫ = ∫ conj(g)·φ` for any `g ∈ L²` and Schwartz `φ`. -/
theorem inner_g_schwartz (g : H2) (φ : SchwartzMap ℝ ℂ) :
    ⟪g, schwartzToL2 φ⟫_ℂ = ∫ x, conj ((g : ℝ → ℂ) x) * (φ : ℝ → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_schwartzToL2 φ] with x hx
  rw [hx, RCLike.inner_apply']

/-- `⟪g, schwartzToL2 (D2 φ)⟫ = ∫ conj(g)·φ″`. -/
theorem inner_g_schwartz_D2 (g : H2) (φ : SchwartzMap ℝ ℂ) :
    ⟪g, schwartzToL2 (D2 φ)⟫_ℂ
      = ∫ x, conj ((g : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x := by
  rw [inner_g_schwartz]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [D2_apply]

/-- Multiplication by `V` acts pointwise a.e. on the Schwartz class. -/
theorem coeFn_potentialMul (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (φ : SchwartzMap ℝ ℂ) :
    (potentialMulCLM V hVc M hV (schwartzToL2 φ) : ℝ → ℂ)
      =ᵐ[volume] fun x => (V x : ℂ) * (φ : ℝ → ℂ) x := by
  unfold potentialMulCLM
  filter_upwards [coeFn_mulLpCLM _ _ _ _ (schwartzToL2 φ), coeFn_schwartzToL2 φ] with x hmul hsch
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hmul
  rw [hmul, hsch]

/-- `⟪g, potentialMulCLM V (schwartzToL2 φ)⟫ = ∫ conj(g)·(V·φ)`. -/
theorem inner_g_potential (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (g : H2) (φ : SchwartzMap ℝ ℂ) :
    ⟪g, potentialMulCLM V hVc M hV (schwartzToL2 φ)⟫_ℂ
      = ∫ x, conj ((g : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_potentialMul V hVc M hV φ] with x hx
  rw [hx, RCLike.inner_apply']

/-! ### The isolated classical regularity fact -/

/-- **The single remaining classical fact: 1D elliptic regularity.**

For continuous real `V`, non-real spectral parameter `z`, and `g ∈ L²(ℝ)`
satisfying the **weak Schrödinger eigen-equation** tested against every Schwartz
function `φ`

    `conj(z) · ∫ conj(g)·φ  =  −∫ conj(g)·φ″ + ∫ conj(g)·(V·φ)`

(the left side is `z̄` times the L² pairing `⟨g, φ⟩`; the right side is the L²
pairing of `g` with the weak action `−φ″ + V·φ` of the operator on the test
function — so the line says `g` distributionally solves `(−d²/dx² + V) g = z g`),
there exists a **classical** L² solution `y` of `−y″ + V y = z y` representing `g`
a.e. This is elliptic/ODE regularity (weak ⇒ `C²`, plus `y, y' ∈ L²`); it is stated
with no operator theory so it is exactly the citable analytic lemma. It is an honest,
satisfiable hypothesis (a true classical theorem), not closed by fiat. -/
def WeakSolutionRegularity (V : ℝ → ℝ) : Prop :=
  ∀ (z : ℂ), z.im ≠ 0 → ∀ (g : H2),
    (∀ φ : SchwartzMap ℝ ℂ,
        conj z * ∫ x, conj ((g : ℝ → ℂ) x) * (φ : ℝ → ℂ) x
          = (-(∫ x, conj ((g : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x))
            + ∫ x, conj ((g : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x)) →
      ∃ (y y' y'' : ℝ → ℂ),
        Brockian.Weyl.Bridge.IsL2Solution V z y y' y'' ∧ (g : ℝ → ℂ) =ᵐ[volume] y

/-! ### The reduction: weak regularity ⇒ the concrete Gate-1 obligation -/

/-- **THE REDUCTION.** For the concrete minimal operator `T = −d²/dx² + V`
(bounded continuous real `V`), the elliptic-regularity hypothesis
`WeakSolutionRegularity V` implies the exact Gate-1 obligation
`DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V`.

The proof does the genuine work around the isolated fact: it unpacks the abstract
adjoint eigen-equation `T* g = z·g` against the dense Schwartz core (via
`LinearPMap.adjoint_isFormalAdjoint`, `schrodingerPMap_toFun_ofInjective`,
`coreMap_apply`, and the integral pairings above) into the concrete weak integral
identity, applies `WeakSolutionRegularity`, and discharges the vanishing clause
`y ≡ 0 ⇒ g = 0` through `Lp.ext`. -/
theorem deficiencyRepresentsODE_of_weakRegularity
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakSolutionRegularity V) :
    Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V := by
  intro z hz g hg
  have heig : (schrodingerPMap V hVc M hV).adjoint g = z • ((g : H2)) :=
    (mem_deficiencySpace_iff (schrodingerPMap V hVc M hV) z g).mp hg
  have hdense := schrodingerPMap_dense V hVc M hV
  -- (a): unpack the abstract adjoint eigen-equation into the concrete weak form
  have hweak : ∀ φ : SchwartzMap ℝ ℂ,
      conj z * ∫ x, conj (((g : H2) : ℝ → ℂ) x) * (φ : ℝ → ℂ) x
        = (-(∫ x, conj (((g : H2) : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x))
          + ∫ x, conj (((g : H2) : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x) := by
    intro φ
    have hFA := LinearPMap.adjoint_isFormalAdjoint hdense g
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective φ)
    rw [heig, inner_smul_left, schrodingerPMap_toFun_ofInjective,
      LinearEquiv.ofInjective_apply, coreMap_apply, inner_add_right, inner_neg_right] at hFA
    rw [inner_g_schwartz (g : H2) φ, inner_g_schwartz_D2 (g : H2) φ,
      inner_g_potential V hVc M hV (g : H2) φ] at hFA
    exact hFA
  -- (b): the isolated regularity fact produces a classical L² solution representing g
  obtain ⟨y, y', y'', hsol, hgy⟩ := hreg z hz (g : H2) hweak
  refine ⟨y, y', y'', hsol, ?_⟩
  -- (c): vanishing of the classical solution forces the L² element to vanish
  intro hy0
  have hg0 : ((g : H2) : ℝ → ℂ) =ᵐ[volume] (⇑(0 : H2)) := by
    filter_upwards [hgy, Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))]
      with x hx hz0
    rw [hx, hy0 x, hz0, Pi.zero_apply]
  exact Lp.ext hg0

/-! ### Gate-1 for the concrete operator, reduced to weak regularity -/

/-- **Gate-1 for the concrete minimal operator, reduced to one classical fact.**
`T = −d²/dx² + V` (bounded continuous real `V`) is essentially self-adjoint given
only `WeakSolutionRegularity V` (1D elliptic regularity). Composes the reduction
`deficiencyRepresentsODE_of_weakRegularity` with the conditional Gate-1 assembly
`schrodinger_essentiallySelfAdjoint_of_ode`. Honest: the sole hypothesis is the
named, satisfiable regularity statement — not hidden, not vacuous. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakSolutionRegularity V) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_ode V hVc M hV
    (deficiencyRepresentsODE_of_weakRegularity V hVc M hV hreg)

/-- Documentary packaging: the concrete Gate-1 state after this reduction — the
elliptic-regularity gap is now a single named analysis hypothesis with no operator
theory in its statement. -/
structure ReducedGate1Status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) where
  /-- The abstract Gate-1 obligation follows from the isolated regularity fact. -/
  reduction : WeakSolutionRegularity V →
    Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V
  /-- ESA follows from the isolated regularity fact. -/
  esa : WeakSolutionRegularity V → EssentiallySelfAdjoint (schrodingerPMap V hVc M hV)

/-- The verified inhabitant of the reduced Gate-1 state. -/
def reduced_gate1_status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    ReducedGate1Status V hVc M hV where
  reduction := deficiencyRepresentsODE_of_weakRegularity V hVc M hV
  esa := schrodinger_essentiallySelfAdjoint_of_weakRegularity V hVc M hV

end Brockian.Weyl.DeficiencyODE

/- ARISTOTLE TARGET — Discharge WeakSolutionRegularity (1D elliptic regularity for continuous V): a weak L2 solution of y''=(V-z)y has a twice-differentiable L2 representative. Closes 2 Gate-1 conditionals. -/
theorem weakSolutionRegularity_of_continuous :
    ∀ (V : ℝ → ℝ), Continuous V → Brockian.Weyl.DeficiencyODE.WeakSolutionRegularity V := by
  sorry
