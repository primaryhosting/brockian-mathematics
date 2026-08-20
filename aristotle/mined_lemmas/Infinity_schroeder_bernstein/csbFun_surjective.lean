/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

universe u v

section CSB

variable {X : Type u} {Y : Type v}

/-- `iterateFun F n x` is the `n`-fold application of `F` to `x`. -/

theorem csbFun_surjective (hg : Function.Injective g) : Function.Surjective (csbFun f g) := by
  intro y
  by_cases hy : leftPart f g (g y)
  · obtain ⟨n, z, hz, hzx⟩ := hy
    cases n with
    | zero => exact absurd (hzx ▸ rfl : g y = z) (hz y)
    | succ m =>
      refine ⟨iterateFun (fun t => g (f t)) m z, ?_⟩
      have hstep : g (f (iterateFun (fun t => g (f t)) m z)) = g y := by
        simpa [iterateFun] using hzx
      have hmem : leftPart f g (iterateFun (fun t => g (f t)) m z) := ⟨m, z, hz, rfl⟩
      rw [csbFun_of_leftPart f g hmem]
      exact hg hstep
  · refine ⟨g y, ?_⟩
    exact hg (csbFun_of_not_leftPart f g hy)

end CSB

/-- **Cantor-Schröder-Bernstein**: if there is an injection `f : X → Y` and an injection
`g : Y → X`, then there is a bijection between `X` and `Y`. -/
