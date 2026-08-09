#!/usr/bin/env python3
"""pca_lean_bridge.py — connect Proof-Carrying Apps to the theorem prover: emit the
SMT isolation-model's soundness properties as REAL Lean 4 targets. These are the
same facts z3_prover decides, now stated as Lean theorems so Aristotle proves them
in the kernel — making the security engine's core machine-checked, not just SMT-checked.

Writes pca_lean_queue.json (fed to night_submit). The abstract model:
    can_access c r := in_scope c r ∨ is_priv c ∨ is_unowned r
mirrors src/formalizer.py's _isolation_smt exactly.
"""
import json
import pathlib

OUT = pathlib.Path(__file__).resolve().parent / "pca_lean_queue.json"

MODEL = (
"section PCA\nvariable {P R : Type}\n"
"def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)\n"
"    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r\n")

THMS = [
 ("PCA.no_escape_no_leak",
  "With no privileged and no unowned escape, any granted access is in-scope: "
  "∀ inScope c r, (∀ c, ¬isPriv c) → (∀ r, ¬isUnowned r) → "
  "canAccess inScope isPriv isUnowned c r → inScope c r."),
 ("PCA.priv_is_escape",
  "A privileged caller always has access (models the admin bypass): "
  "isPriv c → canAccess inScope isPriv isUnowned c r."),
 ("PCA.unowned_is_hole",
  "Any caller can reach an unowned row (models the `IS NULL` hole): "
  "isUnowned r → canAccess inScope isPriv isUnowned c r."),
 ("PCA.escape_monotone",
  "Adding escapes only enlarges access: if inScope c r then canAccess inScope isPriv isUnowned c r."),
 ("PCA.default_deny",
  "With empty scope and no escapes, nothing is accessible: "
  "(∀ c r, ¬inScope c r) → (∀ c, ¬isPriv c) → (∀ r, ¬isUnowned r) → "
  "¬ canAccess inScope isPriv isUnowned c r."),
 ("PCA.leak_iff_escape_when_out_of_scope",
  "Out of scope, access holds iff some escape fires: ¬inScope c r → "
  "(canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r))."),
 ("PCA.owner_only_isolated",
  "Owner-equality scope with no escapes is isolated: let inScope c r := ownerOf r = c; "
  "then canAccess (fun c r => ownerOf r = c) (fun _ => False) (fun _ => False) c r → ownerOf r = c."),
 ("PCA.tightening_refines",
  "Removing the unowned disjunct refines access (subset): "
  "canAccess inScope isPriv (fun _ => False) c r → canAccess inScope isPriv isUnowned c r."),
 ("PCA.no_clean_proved_with_escape",
  "If a clean-isolation proof exists (no cross-scope access) yet an escape can fire out of scope, "
  "contradiction — formalizes the soundness-fuzz invariant: "
  "(∀ c r, canAccess inScope isPriv isUnowned c r → inScope c r) → "
  "(∃ c r, ¬inScope c r ∧ (isPriv c ∨ isUnowned r)) → False."),
 ("PCA.with_check_true_admits_forge",
  "A `WITH CHECK true` write policy admits any row (models forge-any): "
  "let canWrite := fun (_ : P) (_ : R) => True; ∀ c r, canWrite c r."),
]


def main():
    q = []
    for name, stmt in THMS:
        q.append({"target": name, "tier": "PCA-lean", "rank": 1,
                  "goal": "Prove in Lean 4 (Mathlib), axiom-clean. Provide the model definitions inline.",
                  "statement": "Model (state inline):\n" + MODEL + "\nTheorem: " + stmt})
    OUT.write_text(json.dumps({"count": len(q), "queue": q}, indent=1))
    print(f"wrote {OUT} with {len(q)} PCA soundness targets")


if __name__ == "__main__":
    main()
