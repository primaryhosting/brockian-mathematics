import Mathlib
import RequestProject.GlobalWorkspaceFixpoint

/-!
# Global Workspace Fixpoint — Mathlib interface

A restatement of `Frontier.global_workspace_fixpoint` for Mathlib's order-theoretic
hierarchy: on any finite lattice with a bottom element, a monotone (broadcast)
operator has a least fixed point, reached by finitely many iterations from `⊥`.
-/

namespace Frontier

variable {α : Type*} [Fintype α] [Lattice α] [OrderBot α]

/-- The global workspace attached to a monotone operator on a finite Mathlib lattice. -/

theorem countP_lt_countP_of_witness {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      ∀ {a : α}, a ∈ l → p a = false → q a = true → l.countP p < l.countP q := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b t ih =>
      intro h a ha hp hq
      have hmono : t.countP p ≤ t.countP q :=
        List.countP_mono_left (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp ha with rfl | hat
      · simp only [hp, hq, Bool.false_eq_true, if_false, if_true]
        omega
      · have hlt := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hat hp hq
        have hstep : (if p b = true then 1 else 0) ≤ (if q b = true then 1 else 0) := by
          cases hb : p b with
          | false => simp
          | true =>
              have : q b = true := h b (List.mem_cons_self ..) hb
              simp [this]
        have h1 : (if p b = true then 1 else 0) ≤ 1 := by cases p b <;> simp
        have h2 : (if q b = true then 1 else 0) ≤ 1 := by cases q b <;> simp
        omega

open scoped Classical in
/-- The number of states below `a`; a measure of how much has been broadcast. -/
