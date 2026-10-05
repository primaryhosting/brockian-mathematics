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

lemma exists_steer (G : RotGraph n d) (p : Fin n × Fin d) (e : Fin d) :
    ∃ w : ℕ → Fin d, (G.walk w p 3).1 = (G.rot (p.1, e)).1 := by
  obtain ⟨a₁, ha₁⟩ := exists_addOff (G.rot p).2 (G.rot p).2
  obtain ⟨a₂, ha₂⟩ := exists_addOff p.2 e
  refine ⟨fun j => if j = 1 then a₂ else a₁, ?_⟩
  have h1 : G.walk (fun j => if j = 1 then a₂ else a₁) p 1 = G.rot p := by
    show G.stepE _ p = _
    simp only [RotGraph.stepE, if_neg (by norm_num : ¬ (0 : ℕ) = 1), ha₁]
  have h2 : G.walk (fun j => if j = 1 then a₂ else a₁) p 2 = (p.1, e) := by
    show G.stepE _ (G.walk (fun j => if j = 1 then a₂ else a₁) p 1) = _
    rw [h1]
    show ((G.rot (G.rot p)).1, addOff (G.rot (G.rot p)).2 (if (1 : ℕ) = 1 then a₂ else a₁))
        = (p.1, e)
    rw [if_pos rfl, G.rot_involutive p, ha₂]
  show (G.stepE _ (G.walk (fun j => if j = 1 then a₂ else a₁) p 2)).1 = _
  rw [h2]
  rfl

/-- From any state, some finite sequence of offsets drives the exploration walk to any vertex
of the connected component. -/
