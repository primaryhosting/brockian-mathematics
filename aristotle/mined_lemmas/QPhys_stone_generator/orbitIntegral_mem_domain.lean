/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the header above is a
plain block comment; the same header is repeated as a module docstring below.)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint (as an unbounded, i.e. partially
defined, operator).
-/

namespace QPhys

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the infinitesimal generator of a one-parameter group `U`:
the set of vectors `x` for which the orbit map `t ↦ U t x` is differentiable at `0`. -/

lemma orbitIntegral_mem_domain (x : H) (e : ℝ) :
    (∫ s in (0:ℝ)..e, U s x) ∈ generatorDomain U := by
  refine ⟨U e x - x, ?_⟩
  have h0e : HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, U s x) (U e x) (0 + e) := by
    rw [zero_add]
    exact orbitIntegral_hasDerivAt U hUcont x e
  have hA : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..(t + e), U s x) (U e x) 0 :=
    HasDerivAt.comp_add_const 0 e h0e
  have hB : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..t, U s x) x 0 := by
    simpa [hU0] using orbitIntegral_hasDerivAt U hUcont x 0
  have hsub := hA.sub hB
  have hfun : (fun t : ℝ => U t (∫ s in (0:ℝ)..e, U s x))
      = ((fun t : ℝ => ∫ s in (0:ℝ)..(t + e), U s x) - fun t : ℝ => ∫ s in (0:ℝ)..t, U s x) := by
    funext t
    simp only [Pi.sub_apply]
    exact orbitIntegral_translate U hUadd hUcont x t e
  rw [hfun]
  exact hsub

include hU0 hUadd hUcont in
/-- The domain of the generator is dense. -/
