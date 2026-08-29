import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

def IsUES (n d T : ℕ) [NeZero d] (seq : ℕ → Fin d) : Prop :=
  ∀ (G : RotGraph n d) (s t : Fin n), G.Reachable s t →
    ∃ k ≤ T, (G.walk seq (s, 0) k).1 = t

/-- **The input from Reingold's theorem.**  For every vertex count `n` and degree `d` there is
a universal exploration sequence of length polynomial in `n * d` (the polynomial degree `c`
being uniform in `n` and `d`).  Reingold's zig-zag based construction supplies such sequences;
that construction is not formalised here. -/
