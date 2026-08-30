import Mathlib
/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- **Cantor–Schröder–Bernstein**: for types `X` and `Y`, if there is an injection `f : X → Y`
and an injection `g : Y → X`, then there is a bijection `X ≃ Y`.

The proof is Mathlib's `Function.Embedding.schroeder_bernstein`
(equivalently, `Function.Embedding.antisymm`). -/

theorem schroeder_bernstein_bijective {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : X → Y, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein hf hg

/-- A chosen bijection `X ≃ Y` produced from injections in both directions. -/
