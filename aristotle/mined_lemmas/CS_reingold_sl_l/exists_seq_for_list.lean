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

lemma exists_seq_for_list (l : List (RotGraph n d × Fin n × Fin n)) :
    ∃ (T : ℕ) (seq : ℕ → Fin d), ∀ x ∈ l, x.1.Reachable x.2.1 x.2.2 →
      ∃ k ≤ T, (x.1.walk seq (x.2.1, 0) k).1 = x.2.2 := by
  induction l with
  | nil => exact ⟨0, fun _ => 0, by simp⟩
  | cons x l ih =>
      obtain ⟨T, seq, hseq⟩ := ih
      by_cases hx : x.1.Reachable x.2.1 x.2.2
      · set G := x.1
        set s := x.2.1
        set t := x.2.2
        set p := G.walk seq (s, 0) T with hp
        have hreach : G.Reachable p.1 t :=
          (G.reachable_symm (by simpa [hp] using G.walk_reachable seq (s, 0) T)).trans hx
        obtain ⟨L, w, k, hk, hw⟩ := exists_offsets_reach G t hreach p rfl
        refine ⟨T + L, fun j => if j < T then seq j else w (j - T), ?_⟩
        intro y hy hyreach
        rcases List.mem_cons.1 hy with rfl | hy'
        · refine ⟨T + k, by omega, ?_⟩
          rw [G.walk_add]
          have hpre : G.walk (fun j => if j < T then seq j else w (j - T)) (s, 0) T
              = G.walk seq (s, 0) T := G.walk_congr _ _ _ T (fun j hj => by simp [hj])
          rw [hpre, ← hp]
          have hsuf : (fun j => if T + j < T then seq (T + j) else w (T + j - T)) = w := by
            funext j; simp
          rw [hsuf]
          exact hw
        · obtain ⟨k', hk', hw'⟩ := hseq y hy' hyreach
          refine ⟨k', by omega, ?_⟩
          have : y.1.walk (fun j => if j < T then seq j else w (j - T)) (y.2.1, 0) k'
              = y.1.walk seq (y.2.1, 0) k' :=
            y.1.walk_congr _ _ _ k' (fun j hj => by simp [show j < T by omega])
          rw [this]
          exact hw'
      · refine ⟨T, seq, ?_⟩
        intro y hy hyreach
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact absurd hyreach hx
        · exact hseq y hy' hyreach

noncomputable instance : Fintype (RotGraph n d) :=
  Fintype.ofInjective (fun G : RotGraph n d => G.rot) (by
    intro G H h
    cases G; cases H; simpa using h)

/-- **Universal exploration sequences exist** (of some, in general exponential, length).
Reingold's theorem is the much stronger statement that they exist of polynomial length,
which is the content of the hypothesis `CS.HasPolyUES`. -/
