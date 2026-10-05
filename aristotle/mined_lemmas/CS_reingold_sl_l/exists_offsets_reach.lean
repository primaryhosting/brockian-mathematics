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

lemma exists_offsets_reach (G : RotGraph n d) (t : Fin n) {v : Fin n} (hv : G.Reachable v t) :
    ∀ p : Fin n × Fin d, p.1 = v →
      ∃ (L : ℕ) (w : ℕ → Fin d), ∃ k ≤ L, (G.walk w p k).1 = t := by
  induction hv using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun p hp => ⟨0, fun _ => p.2, 0, le_refl 0, hp⟩
  | head hac _ ih =>
      rename_i x c _
      intro p hp
      obtain ⟨e, he⟩ : ∃ e : Fin d, (G.rot (p.1, e)).1 = c := by
        rw [hp]; exact hac
      obtain ⟨w₀, hw₀⟩ := exists_steer G p e
      obtain ⟨L₁, w₁, k₁, hk₁, hw₁⟩ := ih (G.walk w₀ p 3) (by rw [hw₀]; exact he)
      refine ⟨3 + L₁, fun j => if j < 3 then w₀ j else w₁ (j - 3), 3 + k₁, by omega, ?_⟩
      rw [G.walk_add]
      have hpre : G.walk (fun j => if j < 3 then w₀ j else w₁ (j - 3)) p 3 = G.walk w₀ p 3 :=
        G.walk_congr _ _ p 3 (fun j hj => by simp [hj])
      rw [hpre]
      have hsuf : (fun j => if 3 + j < 3 then w₀ (3 + j) else w₁ (3 + j - 3)) = w₁ := by
        funext j
        simp
      rw [hsuf]
      exact hw₁

variable [NeZero d]

/-- Greedy construction: for any finite list of instances there is a single offset sequence
solving all of them. -/
