import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The Wigner–Eckart theorem

Physical setting.  A symmetry algebra (the group algebra of the symmetry group, or the universal
enveloping algebra of its Lie algebra — here an arbitrary `𝕜`-algebra `A`) acts on

* `X`  — the space of *product states* `|k q⟩ ⊗ |j m⟩` (tensor operator component ⊗ initial state),
* `W`  — the final irreducible multiplet `{|j' m'⟩}`, an irreducible (`IsSimpleModule A W`)
  finite-dimensional representation.

An *irreducible tensor operator* is, by definition, an equivariant (`A`-linear) map
`T : X →ₗ[A] W`, and its matrix elements are `⟨j' m'| T |k q; j m⟩ = bra m' (T (ket q m))`.
The *Clebsch–Gordan map* `C : X →ₗ[A] W` is a fixed nonzero equivariant map; its matrix elements
`bra m' (C (ket q m))` are the Clebsch–Gordan coefficients.

The one representation-theoretic input beyond irreducibility is *multiplicity freeness* of the
Clebsch–Gordan series: the final multiplet occurs exactly once in `X`.  This is encoded by
a decomposition `X = V ⊕ N` (`IsCompl V N`) into `A`-submodules where `V` is irreducible (the
unique copy of the final multiplet) and no copy of `W` survives in the complement `N`
(`hN : every A-linear map N → W vanishes`).

Conclusion: the matrix elements factor as
`⟨j' m'| T |k q; j m⟩ = (Clebsch–Gordan coefficient) * r`,
with a single *reduced matrix element* `r` independent of `q`, `m`, `m'`.
-/

namespace Phys

section

variable {𝕜 A W : Type*} [Field 𝕜] [IsAlgClosed 𝕜] [Ring A] [Algebra 𝕜 A]
  [AddCommGroup W] [Module 𝕜 W] [Module A W] [IsScalarTower 𝕜 A W]
  [FiniteDimensional 𝕜 W] [IsSimpleModule A W]

/-- **Schur's lemma, scalar form.** Every equivariant endomorphism of a finite-dimensional
irreducible representation over an algebraically closed field is a scalar. -/
theorem schur_scalar (f : W →ₗ[A] W) : ∃ r : 𝕜, ∀ w, f w = r • w := by
  obtain ⟨r, hr⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed 𝕜 (A := A) (V := W)).2 f
  exact ⟨r, fun w => by rw [← hr]; simp⟩

/-- **Key intermediate lemma (Schur proportionality).**  Any two equivariant maps from an
irreducible representation `V` to an irreducible finite-dimensional representation `W`
(over an algebraically closed field) are proportional, provided the first one is nonzero.
This is the source of the *reduced matrix element*. -/
theorem schur_proportional {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module A V]
    [IsScalarTower 𝕜 A V] [IsSimpleModule A V]
    (c t : V →ₗ[A] W) (hc : c ≠ 0) : ∃ r : 𝕜, ∀ v, t v = r • c v := by
  -- `c` is injective: its kernel is a submodule of the irreducible `V`, and it is not everything.
  have hker : LinearMap.ker c = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.ker c) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hc
  -- `c` is surjective: its range is a nonzero submodule of the irreducible `W`.
  have hrange : LinearMap.range c = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range c) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hc
    · exact h
  let e : V ≃ₗ[A] W :=
    LinearEquiv.ofBijective c ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  obtain ⟨r, hr⟩ := schur_scalar (𝕜 := 𝕜) (t.comp (e.symm : W →ₗ[A] V))
  refine ⟨r, fun v => ?_⟩
  have := hr (e v)
  simpa [e] using this

end

section

variable {𝕜 A X W ιK ιU ιW : Type*} [Field 𝕜] [IsAlgClosed 𝕜] [Ring A] [Algebra 𝕜 A]
  [AddCommGroup X] [Module 𝕜 X] [Module A X] [IsScalarTower 𝕜 A X]
  [AddCommGroup W] [Module 𝕜 W] [Module A W] [IsScalarTower 𝕜 A W]
  [FiniteDimensional 𝕜 W] [IsSimpleModule A W]

/-- **Proportionality of tensor operators.**  Under multiplicity freeness, every equivariant map
`X →ₗ[A] W` is a scalar multiple of the Clebsch–Gordan map `C`. -/
theorem tensor_operator_proportional
    (V N : Submodule A X) (hVN : IsCompl V N) [IsSimpleModule A V]
    (hN : ∀ f : N →ₗ[A] W, f = 0)
    (C T : X →ₗ[A] W) (hC : C ≠ 0) :
    ∃ r : 𝕜, ∀ x : X, T x = r • C x := by
  -- Every equivariant map out of `X` kills the complement `N`.
  have key : ∀ (S : X →ₗ[A] W), ∀ n ∈ N, S n = 0 := by
    intro S n hn
    have h0 := hN (S.comp N.subtype)
    have := congrArg (fun g : N →ₗ[A] W => g ⟨n, hn⟩) h0
    simpa using this
  -- The restriction of `C` to the unique copy `V` of the final multiplet is nonzero.
  have hCV : C.comp V.subtype ≠ 0 := by
    intro h
    apply hC
    ext x
    have hx : x ∈ V ⊔ N := by rw [hVN.sup_eq_top]; trivial
    obtain ⟨v, hv, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
    have hCv : C v = 0 := by
      have := congrArg (fun g : V →ₗ[A] W => g ⟨v, hv⟩) h
      simpa using this
    simp [hCv, key C n hn]
  obtain ⟨r, hr⟩ := schur_proportional (𝕜 := 𝕜) (C.comp V.subtype) (T.comp V.subtype) hCV
  refine ⟨r, fun x => ?_⟩
  have hx : x ∈ V ⊔ N := by rw [hVN.sup_eq_top]; trivial
  obtain ⟨v, hv, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
  have hv' := hr ⟨v, hv⟩
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at hv'
  simp [key T n hn, key C n hn, hv']

/-- **The Wigner–Eckart theorem.**

`T` is an irreducible tensor operator, i.e. an equivariant (`A`-linear) map from the space `X`
of product states `|k q; j m⟩ = ket q m` to the irreducible final multiplet `W`, whose states are
read off by the bras `bra m' : W →ₗ[𝕜] 𝕜`.  `C` is the (nonzero, equivariant) Clebsch–Gordan map,
so that `bra m' (C (ket q m))` is the Clebsch–Gordan coefficient `⟨k q; j m | j' m'⟩`.
Multiplicity freeness of the Clebsch–Gordan series is expressed by the decomposition
`X = V ⊕ N` with `V` irreducible and with no copy of `W` inside `N`.

Then all matrix elements of `T` factor as a Clebsch–Gordan coefficient times a single
*reduced matrix element* `r`, which is independent of `q`, `m` and `m'`. -/
theorem wigner_eckart
    (V N : Submodule A X) (hVN : IsCompl V N) [IsSimpleModule A V]
    (hN : ∀ f : N →ₗ[A] W, f = 0)
    (ket : ιK → ιU → X) (bra : ιW → W →ₗ[𝕜] 𝕜)
    (C T : X →ₗ[A] W) (hC : C ≠ 0) :
    ∃ r : 𝕜, ∀ (q : ιK) (m : ιU) (m' : ιW),
      bra m' (T (ket q m)) = bra m' (C (ket q m)) * r := by
  obtain ⟨r, hr⟩ := tensor_operator_proportional (𝕜 := 𝕜) V N hVN hN C T hC
  refine ⟨r, fun q m m' => ?_⟩
  rw [hr (ket q m), map_smul, smul_eq_mul, mul_comm]

end

/-- An auxiliary fact used to exhibit concrete irreducible representations: if a module is
already irreducible over the base field, it is irreducible over any algebra acting compatibly. -/
theorem simple_of_simple_base {𝕜 A M : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    [AddCommGroup M] [Module 𝕜 M] [Module A M] [IsScalarTower 𝕜 A M]
    [IsSimpleModule 𝕜 M] : IsSimpleModule A M := by
  have hnt : Nontrivial M := IsSimpleModule.nontrivial 𝕜 M
  have : IsSimpleOrder (Submodule A M) := by
    constructor
    intro p
    rcases IsSimpleOrder.eq_bot_or_eq_top (p.restrictScalars 𝕜) with h | h
    · left
      ext x
      constructor
      · intro hx
        have : x ∈ (⊥ : Submodule 𝕜 M) := h ▸ (by exact hx : x ∈ p.restrictScalars 𝕜)
        simpa using this
      · intro hx; simpa using (Submodule.mem_bot A).mp hx ▸ p.zero_mem
    · right
      ext x
      simp only [Submodule.mem_top, iff_true]
      have : x ∈ (⊤ : Submodule 𝕜 M) := Submodule.mem_top
      rw [← h] at this
      exact this
  exact ⟨⟩

/-!
### A non-degenerate instance of the hypotheses

To confirm that the hypotheses of `Phys.wigner_eckart` are consistent and non-degenerate, we
exhibit a concrete symmetry algebra `A₂ = ℂ × ℂ` with two inequivalent one-dimensional
irreducible representations `W₂` (action through the first factor, the "final multiplet") and
`Y₂` (action through the second factor).  The product-state space is `X₂ = W₂ × Y₂`, which
contains exactly one copy of `W₂`, so the multiplicity-freeness hypotheses hold and every
tensor operator `X₂ →ₗ[A₂] W₂` is a multiple of the projection `C = fst`.
-/

namespace Example

/-- The symmetry algebra of the worked example. -/
abbrev A₂ := ℂ × ℂ

/-- The final multiplet: `ℂ`, with `A₂` acting through its first factor. -/
def W₂ := ℂ

/-- A second, inequivalent multiplet: `ℂ`, with `A₂` acting through its second factor. -/
def Y₂ := ℂ

noncomputable instance : AddCommGroup W₂ := inferInstanceAs (AddCommGroup ℂ)
noncomputable instance : Module ℂ W₂ := inferInstanceAs (Module ℂ ℂ)
noncomputable instance : Module A₂ W₂ := Module.compHom ℂ (RingHom.fst ℂ ℂ)
noncomputable instance : AddCommGroup Y₂ := inferInstanceAs (AddCommGroup ℂ)
noncomputable instance : Module ℂ Y₂ := inferInstanceAs (Module ℂ ℂ)
noncomputable instance : Module A₂ Y₂ := Module.compHom ℂ (RingHom.snd ℂ ℂ)

theorem smul_W₂ (a : A₂) (w : W₂) : a • w = (a.1 : ℂ) • (w : ℂ) := rfl

theorem smul_Y₂ (a : A₂) (y : Y₂) : a • y = (a.2 : ℂ) • (y : ℂ) := rfl

noncomputable instance : IsScalarTower ℂ A₂ W₂ :=
  ⟨fun r a w => by
    show ((r • a).1 : ℂ) • (w : ℂ) = r • ((a.1 : ℂ) • (w : ℂ))
    simp [mul_assoc]⟩

noncomputable instance : IsScalarTower ℂ A₂ Y₂ :=
  ⟨fun r a y => by
    show ((r • a).2 : ℂ) • (y : ℂ) = r • ((a.2 : ℂ) • (y : ℂ))
    simp [mul_assoc]⟩

noncomputable instance : FiniteDimensional ℂ W₂ := inferInstanceAs (FiniteDimensional ℂ ℂ)
noncomputable instance : IsSimpleModule ℂ W₂ := inferInstanceAs (IsSimpleModule ℂ ℂ)
noncomputable instance : IsSimpleModule A₂ W₂ := simple_of_simple_base (𝕜 := ℂ)

/-- The space of product states in the worked example. -/
abbrev X₂ := W₂ × Y₂

/-- The unique copy of the final multiplet inside the product-state space. -/
noncomputable def V₂ : Submodule A₂ X₂ := LinearMap.range (LinearMap.inl A₂ W₂ Y₂)

/-- Its invariant complement. -/
noncomputable def N₂ : Submodule A₂ X₂ := LinearMap.range (LinearMap.inr A₂ W₂ Y₂)

theorem V₂_isCompl_N₂ : IsCompl V₂ N₂ := LinearMap.isCompl_range_inl_inr

noncomputable instance : IsSimpleModule A₂ V₂ :=
  IsSimpleModule.congr
    (LinearEquiv.ofInjective (LinearMap.inl A₂ W₂ Y₂) LinearMap.inl_injective).symm

/-- Multiplicity freeness: no copy of the final multiplet survives in the complement. -/
theorem N₂_no_copy_of_W₂ (f : N₂ →ₗ[A₂] W₂) : f = 0 := by
  ext n
  obtain ⟨y, hy⟩ := n.2
  have hfix : ((0 : ℂ), (1 : ℂ)) • n = n := by
    ext
    · show ((0 : ℂ) • ((n : X₂).1) : W₂) = (n : X₂).1
      rw [← hy]; simp [LinearMap.inr_apply]
    · show ((1 : ℂ) • ((n : X₂).2) : Y₂) = (n : X₂).2
      simp
  calc f n = f (((0 : ℂ), (1 : ℂ)) • n) := by rw [hfix]
    _ = ((0 : ℂ), (1 : ℂ)) • f n := by rw [map_smul]
    _ = 0 := by rw [smul_W₂]; simp

/-- The Clebsch–Gordan map of the worked example: projection onto the final multiplet. -/
noncomputable def CG₂ : X₂ →ₗ[A₂] W₂ := LinearMap.fst A₂ W₂ Y₂

theorem CG₂_ne_zero : CG₂ ≠ 0 := by
  intro h
  have : CG₂ ((1 : ℂ), (0 : ℂ)) = 0 := by rw [h]; rfl
  exact one_ne_zero (α := ℂ) this

/-- Wigner–Eckart in the worked example: every tensor operator into the final multiplet is
the Clebsch–Gordan map times a reduced matrix element. -/
theorem wigner_eckart_example (T : X₂ →ₗ[A₂] W₂) :
    ∃ r : ℂ, ∀ x : X₂, T x = r • CG₂ x :=
  Phys.tensor_operator_proportional V₂ N₂ V₂_isCompl_N₂ N₂_no_copy_of_W₂ CG₂ T CG₂_ne_zero

end Example

end Phys

