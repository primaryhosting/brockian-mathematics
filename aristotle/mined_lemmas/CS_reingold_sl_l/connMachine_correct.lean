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

theorem connMachine_correct (hues : IsUES n d T seq) (G : RotGraph n d) (s t : Fin n) :
    (connMachine n d T seq).Accepts G s t ↔ G.Reachable s t := by
  rw [connMachine_accepts_iff]
  constructor
  · rintro ⟨j, -, hjt⟩
    have := G.walk_reachable seq (s, 0) j
    rw [hjt] at this
    exact this
  · intro h
    exact hues G s t h

end Machine

/-! ## Arithmetic auxiliaries -/

