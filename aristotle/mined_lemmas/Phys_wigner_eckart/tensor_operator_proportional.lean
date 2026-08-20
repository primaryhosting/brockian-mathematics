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
