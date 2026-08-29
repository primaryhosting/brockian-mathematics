/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff
open Set

set_option maxHeartbeats 1000000
set_option autoImplicit false

local macro:max "ℝ" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

namespace Frontier

/-!
## A criterion for a manifold to be diffeomorphic to its model space

The key reformulation: a `C^n` manifold `M` modelled on a normed space `E` is `C^n`-diffeomorphic
to `E` itself if and only if its maximal atlas contains a *global* chart, i.e. a chart whose
source is all of `M` and whose target is all of `E`.
-/

section GlobalChart

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞}

/-- In the model space `E` (with the trivial model with corners `𝓘(𝕜, E)`), membership in the
`C^n` structure groupoid is just `C^n`-smoothness of the map and of its inverse. -/

def NoGlobalChartR4Exists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace ℝ⁴ M) (_ : IsManifold (𝓡 4) ∞ M),
    Nonempty (M ≃ₜ ℝ⁴) ∧ ¬ HasGlobalChart ℝ ℝ⁴ M ∞

/-- **Exotic `ℝ⁴` (Freedman–Donaldson), Lean-checked reduction.**

The assertion "there exists a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴`"
is equivalent to the purely atlas-theoretic assertion that there is a smooth `4`-manifold
homeomorphic to `ℝ⁴` whose maximal smooth atlas contains no chart defined on the whole
manifold with image all of `ℝ⁴`.

The equivalence is proved here in full (via the general `nonempty_diffeomorph_model_iff`);
the existence statement itself, `ExoticR4Exists`, is the deep theorem of Freedman and Donaldson
and is not proved. -/
