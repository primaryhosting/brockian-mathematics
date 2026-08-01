"""Emit a LaTeX longtable of the verified registry for the paper (sub-project 2).

Keeps the paper genuinely registry-backed: the theorem census is generated from
registry/theorems.json, never hand-copied. Run: python3 scripts/gen_paper_table.py
Writes paper/registry_table.tex and paper/registry_counts.tex.
"""
from __future__ import annotations

import json
import os


def esc(s: str) -> str:
    return (s.replace("\\", r"\textbackslash{}").replace("_", r"\_")
            .replace("&", r"\&").replace("%", r"\%").replace("#", r"\#"))


def main() -> None:
    reg = json.load(open("registry/theorems.json"))
    thms = [t for t in reg["theorems"] if t["register"] in ("PROVED", "CONDITIONAL")]
    thms.sort(key=lambda t: (t["module"], t["name"]))

    rows = []
    for t in thms:
        short = t["name"].split(".")[-1]
        mod = t["module"].split(".")[-1]
        regi = t["register"]
        axle = t["verification"]["axle"]["verdict"]
        ax = r"\checkmark" if t["verification"]["axioms_ok"] else "--"
        rows.append(f"\\texttt{{{esc(short)}}} & {esc(mod)} & {regi} & {ax} & {axle} \\\\")

    table = [
        r"\begin{longtable}{@{}p{0.44\textwidth}llcc@{}}",
        r"\caption{The verified core: every PROVED/CONDITIONAL declaration in the "
        r"registry, its module, register, whether its \texttt{\#print axioms} is clean "
        r"(only \texttt{propext, Classical.choice, Quot.sound}), and its independent "
        r"AXLE verdict at \texttt{lean-4.32.0}.}\label{tab:registry}\\",
        r"\toprule Theorem & Module & Register & Axioms & AXLE \\ \midrule",
        r"\endfirsthead",
        r"\toprule Theorem & Module & Register & Axioms & AXLE \\ \midrule \endhead",
        *rows,
        r"\bottomrule",
        r"\end{longtable}",
    ]
    os.makedirs("paper", exist_ok=True)
    open("paper/registry_table.tex", "w").write("\n".join(table) + "\n")

    counts = reg["summary"]
    n_thm = sum(1 for t in reg["theorems"] if t["register"] in ("PROVED", "CONDITIONAL"))
    counts_tex = (
        f"\\newcommand{{\\nProved}}{{{counts.get('PROVED',0)}}}\n"
        f"\\newcommand{{\\nConditional}}{{{counts.get('CONDITIONAL',0)}}}\n"
        f"\\newcommand{{\\nConjecture}}{{{counts.get('CONJECTURE',0)}}}\n"
        f"\\newcommand{{\\nDefinition}}{{{counts.get('DEFINITION',0)}}}\n"
        f"\\newcommand{{\\nTheorems}}{{{n_thm}}}\n"
        f"\\newcommand{{\\nModules}}{{{len({t['module'] for t in reg['theorems']})}}}\n"
    )
    open("paper/registry_counts.tex", "w").write(counts_tex)
    print(f"paper table: {n_thm} theorems -> paper/registry_table.tex (+counts)")


if __name__ == "__main__":
    main()
