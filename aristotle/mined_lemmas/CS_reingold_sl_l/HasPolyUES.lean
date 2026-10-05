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

def HasPolyUES : Prop :=
  ∃ c : ℕ, ∀ (n d : ℕ) [NeZero d], ∃ (T : ℕ) (seq : ℕ → Fin d),
    T ≤ (n * d + 1) ^ c ∧ IsUES n d T seq

/-! ## Space bounded machines with query access to the input graph -/

/-- A deterministic machine which decides a property of pairs of vertices of a rotation graph.
It has a finite configuration space `C`; in each step it queries the rotation map at the pair
`query c` and moves to the configuration `next c` applied to the answer.  Space usage is
`log₂ (card C)`. -/
structure Machine (n d : ℕ) where
  /-- The configuration type. -/
  C : Type
  /-- The configuration type is finite. -/
  fintypeC : Fintype C
  /-- The initial configuration on the query pair `(s, t)`. -/
  init : Fin n → Fin n → C
  /-- The rotation-map entry queried in the current configuration. -/
  query : C → Fin n × Fin d
  /-- The transition function, fed with the answer to the query. -/
  next : C → Fin n × Fin d → C
  /-- The accepting configurations. -/
  accept : C → Bool

namespace Machine

variable {n d : ℕ}

/-- The number of configurations; the space used by the machine is `log₂` of this. -/
