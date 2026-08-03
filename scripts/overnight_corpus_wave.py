#!/usr/bin/env python3
"""Overnight epic corpus wave generator + AXLE attester.

Usage:
  source ~/.openclaw/vault-bridges.env
  python3 scripts/overnight_corpus_wave.py --gaps-start 132 --gaps-end 160 \\
      --cos 59 61 67 --k2 43 47

Then:
  python3 scripts/gen_registry.py
  python3 scripts/export_public_registry.py
  cp torus/public/verified-registry.json deploy/torus-lovable/public/
  # surgical git add of new files only + commit + push
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
B = ROOT / "Brockian"

# Minimal English names for even integers we care about (extend as needed)
def number_word(n: int) -> str:
    ones = {
        0: "zero", 1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
        6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten", 11: "eleven",
        12: "twelve", 13: "thirteen", 14: "fourteen", 15: "fifteen",
        16: "sixteen", 17: "seventeen", 18: "eighteen", 19: "nineteen",
    }
    tens = {
        2: "twenty", 3: "thirty", 4: "forty", 5: "fifty",
        6: "sixty", 7: "seventy", 8: "eighty", 9: "ninety",
    }
    if n < 20:
        return ones[n]
    if n < 100:
        t, o = divmod(n, 10)
        return tens[t] if o == 0 else tens[t] + ones[o].capitalize()
    if n < 200:
        rest = n - 100
        if rest == 0:
            return "oneHundred"
        return "oneHundred" + number_word(rest)[0].upper() + number_word(rest)[1:]
    if n < 1000:
        h, rest = divmod(n, 100)
        base = ones[h] + "Hundred"
        if rest == 0:
            return base
        return base + number_word(rest)[0].upper() + number_word(rest)[1:]
    if n < 1_000_000:
        th, rest = divmod(n, 1000)
        base = number_word(th) + "Thousand"
        if rest == 0:
            return base
        return base + number_word(rest)[0].upper() + number_word(rest)[1:]
    raise ValueError(f"no word for {n}")


def camel_prime(p: int) -> tuple[str, str]:
    """(Name, camel) e.g. (FiftyNine, fiftyNine)."""
    w = number_word(p)
    name = w[0].upper() + w[1:]
    return name, w[0].lower() + w[1:] if w[0].isupper() else w


def gaps_file(ns: list[int], tag: str) -> str:
    body: list[str] = []
    header = f'''/-
  Brockian/SingularSeriesGaps{tag}.lean — even binary gaps n ∈ {{{", ".join(map(str, ns))}}}.

  HONEST SCOPE: finite/local singular-series arithmetic only.
  Does NOT claim twin-prime / HL asymptotics / Goldbach transfer / infinitude.
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples
import Brockian.SingularSeriesMoreExamples

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples
open Brockian.SingularSeries.MoreExamples

namespace Brockian.SingularSeries.Gaps{tag}

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

'''
    for n in ns:
        w = number_word(n)
        body += [
            f"theorem evenPair_card_{w} : (evenPair {n}).card = 2 :=",
            f"  evenPair_card_of_ne_zero (by decide : ({n} : ℕ) ≠ 0)",
            "",
        ]
    for n in ns:
        w = number_word(n)
        body += [
            f"theorem isAdmissible_evenPair_{w} : IsAdmissible (evenPair {n}) :=",
            f"  isAdmissible_evenPair (by decide : Even {n})",
            "",
        ]
    for n in ns:
        w = number_word(n)
        body += [
            f"theorem singular_series_pos_evenPair_{w} : 0 < singularSeries (evenPair {n}) :=",
            f"  singular_series_pos_evenPair (by decide : Even {n})",
            "",
        ]
    for n in ns:
        w = number_word(n)
        body += [
            f"theorem singular_series_finite_pos_evenPair_{w} (P : ℕ) :",
            f"    0 < singularSeriesFinite (evenPair {n}) P :=",
            f"  singular_series_finite_pos_evenPair (by decide : Even {n}) P",
            "",
        ]
    for n in ns:
        w = number_word(n)
        body += [
            f"theorem nu_p_{w} (p : ℕ) (hp : Nat.Prime p) :",
            f"    nu_p (evenPair {n}) p = if p = 2 ∨ p ∣ {n} then 1 else 2 :=",
            f"  nu_p_evenPair (by decide : ({n} : ℕ) ≠ 0) (by decide : Even {n}) hp",
            "",
        ]
    for n in (ns[0], ns[-1]):
        w = number_word(n)
        body += [
            f"theorem nu_p_{w}_two : nu_p (evenPair {n}) 2 = 1 :=",
            f"  nu_p_evenPair_two (by decide : Even {n})",
            "",
            f"theorem localFactor_{w}_two : localFactor (evenPair {n}) 2 = 2 :=",
            f"  localFactor_evenPair_two (by decide : ({n} : ℕ) ≠ 0) (by decide : Even {n})",
            "",
        ]
    body.append(f"end Brockian.SingularSeries.Gaps{tag}\n")
    return header + "\n".join(body)


def cos_file(p: int) -> str:
    name, camel = camel_prime(p)
    deg = (p - 1) // 2
    return f'''/-
  Brockian/CosTraceNorm{name}.lean — spectral generator at p = {p}.

  [ℚ(2 cos 2π/{p}):ℚ] = {deg} via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNorm{name}

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_{camel} : Nat.Prime {p} := by decide

theorem {camel}_ne_two : ({p} : ℕ) ≠ 2 := by decide

theorem degree_{camel} : (minpoly ℚ (spectralGen {p})).natDegree = {deg} :=
  real_subfield_degree prime_{camel} {camel}_ne_two

theorem isIntegral_spectralGen_{camel} : IsIntegral ℤ (spectralGen {p}) :=
  isIntegral_spectralGen prime_{camel}

theorem isIntegral_spectralGen_{camel}_Q : IsIntegral ℚ (spectralGen {p}) :=
  isIntegral_spectralGen_ℚ prime_{camel}

theorem isIntegral_and_degree_{camel} :
    IsIntegral ℤ (spectralGen {p}) ∧
      (minpoly ℚ (spectralGen {p})).natDegree = {deg} :=
  ⟨isIntegral_spectralGen_{camel}, degree_{camel}⟩

theorem {camel}_pack :
    IsIntegral ℤ (spectralGen {p}) ∧
      (minpoly ℚ (spectralGen {p})).natDegree = {deg} :=
  isIntegral_and_degree_{camel}

end Brockian.CosTraceNorm{name}
'''


def k2_file(p: int) -> str:
    m = p - 1
    a, b = m**3 + 1, m**3
    c, d = m**4 - 1, m**4
    _, w = camel_prime(p)
    return f'''/-
  Brockian/GoldbachWheelK2_{p}.lean — exact local product K₂·K_{p}.

  HONEST SCOPE: finite local covariance product only. Not Goldbach.
  K_{p} from def: 1 ± 1/(p−1)^{{3 or 4}} with p={p} → (p−1)={m}.
-/
import Mathlib
import Brockian.GoldbachComb
import Brockian.GoldbachParity

set_option autoImplicit false
-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.Goldbach.WheelK2_{p}

open Brockian.GoldbachComb
open Brockian.Goldbach.Parity

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance : Fact (Nat.Prime {p}) := ⟨by decide⟩

theorem Kp_{w}_of_dvd {{h : ℤ}} (hh : ({p} : ℤ) ∣ h) :
    Kp {p} h = ({a} / {b} : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_{w}_of_not_dvd {{h : ℤ}} (hh : ¬({p} : ℤ) ∣ h) :
    Kp {p} h = ({c} / {d} : ℚ) := by
  simp [Kp, hh]
  norm_num

theorem Kp_{w} (h : ℤ) :
    Kp {p} h = if ({p} : ℤ) ∣ h then ({a} / {b} : ℚ) else ({c} / {d} : ℚ) := by
  split_ifs with hh
  · exact Kp_{w}_of_dvd hh
  · exact Kp_{w}_of_not_dvd hh

def K2_{p} (h : ℤ) : ℚ := Kp 2 h * Kp {p} h

theorem K2_{p}_of_not_two_dvd {{h : ℤ}} (h2 : ¬(2 : ℤ) ∣ h) : K2_{p} h = 0 := by
  simp [K2_{p}, Kp_two_of_not_dvd h2]

theorem K2_{p}_of_two_and_{w}_dvd {{h : ℤ}}
    (h2 : (2 : ℤ) ∣ h) (hp : ({p} : ℤ) ∣ h) :
    K2_{p} h = (2 : ℚ) * ({a} / {b}) := by
  simp [K2_{p}, Kp_two_of_dvd h2, Kp_{w}_of_dvd hp]

theorem K2_{p}_eq (h : ℤ) :
    K2_{p} h =
      (if (2 : ℤ) ∣ h then (2 : ℚ) else 0) *
      (if ({p} : ℤ) ∣ h then ({a} / {b} : ℚ) else ({c} / {d} : ℚ)) := by
  simp [K2_{p}, Kp_two h, Kp_{w} h]

end Brockian.Goldbach.WheelK2_{p}
'''


def ensure_import(text: str, after: str, new_line: str) -> str:
    if new_line in text:
        return text
    if after not in text:
        raise SystemExit(f"missing import anchor: {after}")
    return text.replace(after, after + "\n" + new_line, 1)


def attest(path: str, ns: str, stem: str) -> tuple[bool, int]:
    src = Path(path).read_text()
    names = re.findall(r"^\s*(?:theorem|lemma|def)\s+(\w+)", src, re.M)
    print(f"ATTEST {stem} ({len(names)})...", flush=True)
    r = subprocess.run(
        ["python3", str(ROOT / "scripts/attest.py"), path, ns, *names, "--env", "lean-4.32.0"],
        cwd=ROOT, capture_output=True, text=True,
    )
    default = ROOT / "registry/attestations" / f"{ns.split('.')[-1]}.json"
    final = ROOT / "registry/attestations" / f"{stem}.json"
    if default.exists() and default != final:
        default.replace(final)
    if not final.exists():
        print((r.stderr or r.stdout)[-800:])
        return False, 0
    att = json.loads(final.read_text())
    mv = bool(att.get("module_verified"))
    n = len(att.get("declarations") or [])
    print(f"  -> verified={mv} decls={n} code={r.returncode}", flush=True)
    if not mv:
        print((r.stderr or r.stdout)[-600:])
    return mv, n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--gaps-start", type=int, default=0)
    ap.add_argument("--gaps-end", type=int, default=0, help="inclusive even end")
    ap.add_argument("--cos", type=int, nargs="*", default=[])
    ap.add_argument("--k2", type=int, nargs="*", default=[])
    ap.add_argument("--no-attest", action="store_true")
    args = ap.parse_args()

    mods: list[tuple[str, str, str]] = []  # path, ns, stem
    bl = (ROOT / "Brockian.lean").read_text()

    if args.gaps_start and args.gaps_end:
        evens = list(range(args.gaps_start if args.gaps_start % 2 == 0 else args.gaps_start + 1,
                           args.gaps_end + 1, 2))
        for i in range(0, len(evens), 5):
            chunk = evens[i:i + 5]
            if len(chunk) < 5:
                break
            tag = f"{chunk[0]}{chunk[-1]}"
            path = B / f"SingularSeriesGaps{tag}.lean"
            path.write_text(gaps_file(chunk, tag))
            print("wrote", path.name)
            imp = f"import Brockian.SingularSeriesGaps{tag}"
            # anchor: last existing gaps import or Gaps92100
            for anchor in (
                "import Brockian.SingularSeriesGaps122130",
                "import Brockian.SingularSeriesGaps92100",
                "import Brockian.SingularSeriesGaps6270",
            ):
                if anchor in bl or anchor.replace("import ", "") in bl:
                    bl = ensure_import(bl, anchor if anchor in bl else
                                       [a for a in bl.splitlines() if a.startswith("import Brockian.SingularSeriesGaps")][-1],
                                       imp)
                    break
            else:
                # append after any gaps import
                gaps_imps = [ln for ln in bl.splitlines() if ln.startswith("import Brockian.SingularSeriesGaps")]
                if not gaps_imps:
                    raise SystemExit("no Gaps import anchor")
                bl = ensure_import(bl, gaps_imps[-1], imp)
            mods.append((str(path), f"Brockian.SingularSeries.Gaps{tag}", f"SingularSeriesGaps{tag}"))

    for p in args.cos:
        name, _ = camel_prime(p)
        path = B / f"CosTraceNorm{name}.lean"
        path.write_text(cos_file(p))
        print("wrote", path.name)
        imp = f"import Brockian.CosTraceNorm{name}"
        cos_imps = [ln for ln in bl.splitlines() if ln.startswith("import Brockian.CosTraceNorm")]
        bl = ensure_import(bl, cos_imps[-1], imp)
        mods.append((str(path), f"Brockian.CosTraceNorm{name}", f"CosTraceNorm{name}"))

    for p in args.k2:
        path = B / f"GoldbachWheelK2_{p}.lean"
        path.write_text(k2_file(p))
        print("wrote", path.name)
        imp = f"import Brockian.GoldbachWheelK2_{p}"
        k_imps = [ln for ln in bl.splitlines() if ln.startswith("import Brockian.GoldbachWheelK2")]
        bl = ensure_import(bl, k_imps[-1], imp)
        mods.append((str(path), f"Brockian.Goldbach.WheelK2_{p}", f"GoldbachWheelK2_{p}"))

    (ROOT / "Brockian.lean").write_text(bl)

    if args.no_attest:
        return 0

    ok_all = True
    total = 0
    for path, ns, stem in mods:
        # skip if already green
        attp = ROOT / "registry/attestations" / f"{stem}.json"
        if attp.exists():
            att = json.loads(attp.read_text())
            if att.get("module_verified"):
                print(f"skip green {stem}")
                total += len(att.get("declarations") or [])
                continue
        mv, n = attest(path, ns, stem)
        ok_all = ok_all and mv
        if mv:
            total += n
    print("ALL_GREEN", ok_all, "DECLS", total)
    return 0 if ok_all else 1


if __name__ == "__main__":
    raise SystemExit(main())
