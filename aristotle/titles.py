#!/usr/bin/env python3
"""titles.py — human-readable naming for proof targets.

Humans can't scan `Brockian.CosTraceNorm1279` or `Math.abel_ruffini_deg5` in a PR
list or Aristotle dashboard. This turns a target id + its domain tier into:
  - category(tier)     -> friendly category/theme  ("Pure Mathematics")
  - human_name(target) -> Title-Cased readable name ("Abel Ruffini Deg 5")
  - title(target,tier) -> "Category — Human Name"   (the one-line human title)
  - header(...)        -> a Lean doc-comment block to prepend to a proof file
Shared by annotate_headers.py (PR files) and night_submit.py (submission titles).
"""
import re

CATEGORY = {
    "DOMAIN-math": "Pure Mathematics",
    "DOMAIN-qc": "Quantum Computing",
    "DOMAIN-chem": "Chemistry",
    "DOMAIN-cs": "Computer Science",
    "DOMAIN-qphys": "Quantum Physics",
    "C-corpus-extension": "Brockian Corpus",
    "A1-discharge-literature": "Brockian (Literature Discharge)",
    "A2-discharge-open": "Brockian (Open Discharge)",
    "B-conjecture": "Brockian Conjecture",
    "D-pca-meta": "Proof-Carrying Apps",
    "PCA-lean": "Proof-Carrying Apps (Lean)",
    "FRONTIER-set": "Frontier — Set Theory",
    "FRONTIER-primes": "Frontier — Prime Numbers",
    "FRONTIER-moonshot": "Frontier — Moonshot",
    "FRONTIER-fields": "Frontier — Fields Medal Work",
    "FRONTIER-spectral": "Frontier — Spectral Geometry",
    "FRONTIER-betrothed": "Frontier — Betrothed Numbers",
    "FRONTIER-linalg": "Zeta-23 §3 Linear Algebra (re-derivation)",
    "FRONTIER-riemann": "Riemann Program",
    "FRONTIER-fib": "Fibonacci",
    "FRONTIER-wave2": "Frontier Wave 2 (deeper machinery)",
}


def category(tier):
    if not tier:
        return "Mathematics"
    return CATEGORY.get(tier, tier.replace("-", " ").title())


def human_name(target):
    """Last dotted component, de-snake/de-camel-cased to Title Case words."""
    last = (target or "").split(".")[-1]
    # split snake_case and camelCase / digit boundaries
    s = re.sub(r"_", " ", last)
    s = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", s)
    s = re.sub(r"(?<=[A-Za-z])(?=[0-9])", " ", s)
    s = re.sub(r"(?<=[0-9])(?=[A-Za-z])", " ", s)
    words = [w for w in s.split() if w]
    return " ".join(w if w.isupper() else w.capitalize() for w in words) or last


def title(target, tier):
    return f"{category(tier)} — {human_name(target)}"


def header(target, tier, statement=None, verified=True):
    """A Lean `/-! ... -/` module doc block naming the problem, for humans."""
    lines = ["/-!", f"# {human_name(target)}", f"Category: {category(tier)}",
             f"Target: {target}"]
    if statement:
        stmt = " ".join(statement.split())
        if len(stmt) > 400:
            stmt = stmt[:397] + "..."
        lines.append(f"Statement: {stmt}")
    lines.append("Verification: AXLE cloud compile (Lean 4.32.0, Mathlib); "
                 "imported axiom dependencies not enumerated"
                 if verified else "Verification: pending")
    lines.append("Provenance: Aristotle theorem prover (Harmonic)")
    lines.append("-/")
    return "\n".join(lines)


if __name__ == "__main__":
    for t, tier in [("Math.abel_ruffini_deg5", "DOMAIN-math"),
                    ("Brockian.CosTraceNorm1279", "C-corpus-extension"),
                    ("CS.church_rosser_beta_diamond", "DOMAIN-cs"),
                    ("Frontier.Brun_twin_reciprocal", "FRONTIER-primes")]:
        print(title(t, tier))
