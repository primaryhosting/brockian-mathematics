/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring; the required header is
-- reproduced verbatim as the module docstring immediately below the import.)

import RequestProject.Math2.Canonical

/-!
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

For a smooth projective curve, described here through its function field `F / K` with its
family of places `P` (see `Math2.PreCurve` and `Math2.PreCurve.IsCurve`), there exists a
*canonical divisor* `W` such that for every divisor `D`

  `ℓ(D) - ℓ(W - D) = deg D + 1 - g`,

where `ℓ(D) = dim_K L(D)` is the dimension of the Riemann-Roch space of `D`, `deg D` is the
degree of `D` and `g` is the genus of the curve.  The canonical divisor moreover satisfies
`ℓ(W) = g` and `deg W = 2g - 2`.
-/

namespace Math2

open PreCurve

variable {K : Type u} {F : Type v} {P : Type w} [Field K] [Field F] [Algebra K F]

/-- **Riemann-Roch for a smooth projective curve.**

There is a canonical divisor `W` (of degree `2g - 2` and with `ℓ(W) = g`) such that for every
divisor `D` on the curve,
`ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/

lemma ker_resQuotMap_eq_ker_psi (D : P →₀ ℤ) (p : P) :
    LinearMap.ker (C.resQuotMap (D + Finsupp.single p 1) p) =
      LinearMap.ker (C.psi D (D + Finsupp.single p 1)) := by
  ext α
  simp only [LinearMap.mem_ker, resQuotMap, psi, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.coe_subtype]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    have hβmem : C.diagLin (x : F) ∈ C.AD (D + Finsupp.single p 1) :=
      (C.diagLin_mem_AD_iff _ _).2 x.2
    have hres : C.resA (D + Finsupp.single p 1) p
        (α - ⟨C.diagLin (x : F), hβmem⟩) = 0 := by
      simp only [map_sub, C.resA_diagLin _ p x, hx, sub_self]
    rw [C.resA_eq_zero_iff] at hres
    have hmem : (α : C.Adele) - C.diagLin (x : F) ∈ C.AD D := by
      simpa using hres
    have hsplit : (α : C.Adele) = ((α : C.Adele) - C.diagLin (x : F)) + C.diagLin (x : F) :=
      (sub_add_cancel _ _).symm
    rw [hsplit]
    exact Submodule.add_mem_sup hmem ⟨(x : F), rfl⟩
  · intro h
    rw [Submodule.mem_sup] at h
    obtain ⟨a, ha, f, hf, haf⟩ := h
    obtain ⟨x, hx⟩ := hf
    subst hx
    have hamem : a ∈ C.AD (D + Finsupp.single p 1) := C.AD_mono (le_add_single D p) ha
    have hfmemE : C.diagLin x ∈ C.AD (D + Finsupp.single p 1) := by
      have hval : C.diagLin x = (α : C.Adele) - a := by rw [← haf]; abel
      rw [hval]
      exact Submodule.sub_mem _ α.2 hamem
    have hxL : x ∈ C.LSpace (D + Finsupp.single p 1) := (C.diagLin_mem_AD_iff _ x).1 hfmemE
    have hsplit : α = ⟨a, hamem⟩ + ⟨C.diagLin x, hfmemE⟩ := by
      apply Subtype.ext
      exact haf.symm
    have hzero : C.resA (D + Finsupp.single p 1) p ⟨a, hamem⟩ = 0 := by
      rw [C.resA_eq_zero_iff]
      simpa using ha
    refine ⟨⟨x, hxL⟩, ?_⟩
    rw [hsplit, map_add, hzero, zero_add]
    exact (C.resA_diagLin _ p ⟨x, hxL⟩).symm

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `range ψ ≅ resField p / L(E)`. -/
