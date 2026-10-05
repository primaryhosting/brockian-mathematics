import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Topology Complex
open scoped LinearPMap

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U : ℝ → (H →L[ℂ] H)` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, each `U t` norm
preserving (hence unitary, since the group law provides the inverse `U (-t)`), and such that
`t ↦ U t x` is continuous for every `x` (strong continuity). -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => U t x

omit [CompleteSpace H] in
/-- Sanity check that the hypotheses are satisfiable: the constant family `U t = 1` is a
strongly continuous one-parameter unitary group. -/

theorem dense_genDomain {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    Dense ((gen U).domain : Set H) := by
  have hbot : (genDomain U)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨x, hx⟩ := surjective_gen_add_I hU y
    have hxy : inner ℂ (x : H) y = 0 :=
      inner_eq_zero_symm.1 ((Submodule.mem_orthogonal' _ _).1 hy _ x.2)
    rw [← hx, inner_add_right, inner_smul_right] at hxy
    have hreal : (starRingEnd ℂ) (inner ℂ (x : H) (gen U x)) = inner ℂ (x : H) (gen U x) := by
      rw [inner_conj_symm]
      exact gen_isFormalAdjoint hU x x
    have him : (inner ℂ (x : H) (gen U x)).im = 0 := Complex.conj_eq_iff_im.1 hreal
    have hxx : (inner ℂ (x : H) (x : H) : ℂ) = ((‖(x : H)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_num
    rw [hxx] at hxy
    have hnorm : ‖(x : H)‖ ^ 2 = 0 := by
      have h1 := congrArg Complex.im hxy
      simp only [Complex.add_im, him, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, Complex.ofReal_re, Complex.zero_im] at h1
      linarith
    have hx0 : (x : H) = 0 :=
      norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hnorm)
    have hx0' : x = 0 := Subtype.ext hx0
    have hy0 : y = 0 := by
      rw [← hx, hx0']
      simp
    simpa using hy0
  have htop : (genDomain U).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 hbot
  rw [show ((gen U).domain : Set H) = ((genDomain U : Submodule ℂ H) : Set H) from rfl,
    dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, htop]
  simp

/-- **Stone's theorem**: the generator of a strongly continuous one-parameter unitary group
on a complex Hilbert space is a self-adjoint (unbounded) operator. -/
