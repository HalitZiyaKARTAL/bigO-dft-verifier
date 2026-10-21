"""Exact scalar audit; no Lean or universal matroid verification. Python 3.9+."""

import argparse
from fractions import Fraction as Q
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import urllib.request
import zipfile
import zlib


ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(name):
    return json.loads((ROOT / name).read_text())


def audit(parameters, expected, log_terms=4, endpoint=141):
    p = {key: Q(value) for key, value in parameters.items()}
    k, rho, h, t = (p[key] for key in ("kappa", "rho", "h", "t"))
    mu, nu, a, b, v, d = (p[key] for key in ("mu", "nu", "a", "b", "v", "d"))
    theta, levels = p["theta"], p["levels"]
    K = k + nu
    prob = rho + (1 - rho) * t
    zeta = (1 - prob) / (1 + prob)
    log_lower = 2 * sum((zeta ** (2*j + 1) / (2*j + 1)
                         for j in range(log_terms)), Q(0))
    activation = (Q(2, 3)*a*(1/rho - 1) + b)/(1+a) + 2*v
    gamma = rho/4 - activation/d
    epsilon = mu*rho/k + a/d
    a0 = 1/d
    residue = K*t + K*rho/k

    def saving(x):
        return (1-h)*(gamma - (epsilon + K*t + residue/(x-1))/h)

    def coefficient(x):
        return (1-t)*((x-1)/x)**2*t*saving(x)/(levels*(theta-1)*K)

    x = Q(endpoint)
    c141, c140 = coefficient(x), coefficient(Q(140))
    relative_gain = c141/c140-1 if c140 else None
    A = rho*(3 + 4*v/3)
    B = theta ** int(levels)
    checks = {
        "parameter_domains": (all(value > 0 for value in p.values())
                              and all(0 < value < 1 for value in (rho, h, t))
                              and theta > 1 and levels.denominator == 1),
        "p_exact": prob == Q(expected["p"]),
        "p_quarter_bound": prob > Q(3, 4)**4,
        "generator_tilt": A**8 * prob**105 < (a*v)**8,
        "witness_tilt": (1-prob)**8 * prob**113 < (b*v)**8,
        "log_series_domain": 0 < prob < 1 and 0 < zeta < 1,
        "log_lower": log_lower > d > 0,
        "B_greater_than_endpoint": B > x,
        "gamma_exact": gamma == Q(expected["gamma"]),
        "epsilon_exact": epsilon == Q(expected["epsilon"]),
        "a0_exact": a0 == Q(expected["a0"]),
        "positive_gamma": 0 < gamma <= rho/4,
        "saving_exact": saving(x) == Q(expected["s141"]),
        "positive_saving": saving(x) > 0,
        "maximum_branch_cancellation": (1-t)*(gamma*k+a0)/K < Q(1, 4),
        "C141_exact": c141 == Q(expected["C141"]),
        "C140_is_predecessor": c140 == Q(expected["Cstar"]),
        "strict_improvement": c141 > c140,
        "difference_exact": c141-c140 == Q(expected["difference"]),
        "relative_improvement_exact": relative_gain == Q(expected["relative_gain"]),
        "phase_denominator": levels*(theta-1) == 5,
        "monotonicity_factors_positive": residue > 0 and (1-h)/h > 0 and x > 1,
        "payoff_prefactor_positive": (1-t)*t/(levels*(theta-1)*K) > 0,
        "actual_B_payoff_exceeds_endpoint": coefficient(B) > c141,
        "comparison_chain": c141 > c140 > Q(1, 2**38) > Q(1, 2**293) > Q(1, 2**310),
    }
    values = {"C141": str(c141), "Cstar": str(c140),
              "difference": str(c141-c140), "relative_gain": str(relative_gain)}
    return checks, values


def controls(parameters, expected):
    cases = []
    for name, key, value, failure in [
        ("changed_rho", "rho", "94/256", "p_exact"),
        ("zero_t", "t", "0", "C141_exact"),
        ("insufficient_generator_budget", "a", "1/8640", "generator_tilt"),
        ("wrong_phase_count", "levels", "255", "phase_denominator"),
    ]:
        changed = dict(parameters, **{key: value})
        cases.append((name, audit(changed, expected)[0], failure))
    wrong = dict(expected, C141=str(Q(expected["C141"])+Q(1, Q(expected["C141"]).denominator)))
    cases.append(("wrong_certificate", audit(parameters, wrong)[0], "C141_exact"))
    wrong = dict(expected, difference=str(-Q(expected["difference"])))
    cases.append(("wrong_difference_sign", audit(parameters, wrong)[0], "difference_exact"))
    cases.append(("one_log_term", audit(parameters, expected, log_terms=1)[0], "log_lower"))
    cases.append(("unjustified_endpoint_142", audit(parameters, expected, endpoint=142)[0],
                  "B_greater_than_endpoint"))
    result = {}
    for name, checks, failure in cases:
        require(not checks[failure], "negative control was not detected: " + name)
        result[name] = {"detected": True, "required_failed_check": failure}
    return result


def check_manifest():
    manifest = load("MANIFEST.json")
    require(manifest["algorithm"] == "sha256", "wrong manifest algorithm")
    actual = {}
    for path in ROOT.rglob("*"):
        require(not path.is_symlink(), "symlink in package")
        if path.is_file() and path != ROOT / "MANIFEST.json":
            actual[path.relative_to(ROOT).as_posix()] = digest(path.read_bytes())
    require(actual == manifest["sha256"], "manifest inventory or digest mismatch")


def check_source(pdf_path, fetch, pins, expected):
    source = pins["paper"]
    if fetch:
        with urllib.request.urlopen(source["url"], timeout=30) as response:
            pdf = response.read(1_000_001)
    else:
        pdf = pdf_path.read_bytes()
    require(len(pdf) == source["bytes"] and digest(pdf) == source["sha256"],
            "source PDF pin mismatch")

    # This extracts the one known stream from these hash-pinned bytes. It is
    # intentionally not a general PDF parser. The attachment is a page-13
    # FileAttachment (/FS /EF /F), absent from the catalog EmbeddedFiles list.
    start = pdf.index(b"\n215 0 obj\n")
    marker = pdf.index(b"stream\n", start)
    header = pdf[start:marker]
    require(re.search(rb"/Filter\s*/FlateDecode", header), "unexpected PDF filter")
    length = int(re.search(rb"/Length\s+(\d+)", header).group(1))
    require(length == 6655, "unexpected embedded stream length")
    attachment = zlib.decompress(pdf[marker+7:marker+7+length])
    require(digest(attachment) == pins["attachment"]["sha256"], "attachment pin mismatch")
    replay = {}
    with zipfile.ZipFile(io.BytesIO(attachment)) as archive, tempfile.TemporaryDirectory() as temp:
        for name, sha in pins["attachment"]["scripts"].items():
            content = archive.read(name)
            require(digest(content) == sha, "author checker pin mismatch: " + name)
            script = Path(temp) / Path(name).name
            script.write_bytes(content)
            run = subprocess.run([sys.executable, "-I", "-S", "-B", str(script)],
                                 cwd=temp, env={"PATH": os.defpath},
                                 capture_output=True, text=True, timeout=10, check=True)
            result = json.loads(run.stdout)
            if name.endswith("check_scalar.py"):
                require(len(result["checks"]) == 15 and all(result["checks"].values()),
                        "author scalar checks failed")
                for key in ("C141", "Cstar", "difference"):
                    require(Q(result[key]) == Q(expected[key]), "author scalar value mismatch")
                count = 15
            else:
                require(len(result["strict_comparisons"]) == 4
                        and all(result["strict_comparisons"].values()), "author comparisons failed")
                require(Q(result["relative_improvement_over_Cstar"]) == Q(expected["relative_gain"]),
                        "author relative improvement mismatch")
                count = 4
            replay[name] = {"sha256": sha, "passed_checks": count,
                            "stdout_sha256": digest(run.stdout.encode())}
    return {"pdf_sha256": digest(pdf), "attachment_sha256": digest(attachment),
            "author_checker_replay": replay}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--fetch-source", action="store_true")
    group.add_argument("--source-pdf", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    check_manifest()
    data = load("data/parameters.json")
    checks, values = audit(data["parameters"], data["expected"])
    require(all(checks.values()), "independent audit failed: " +
            ", ".join(key for key, value in checks.items() if not value))
    report = {"status": "PASS: scalar arithmetic only", "checks": checks,
              "values": values, "negative_controls": controls(data["parameters"], data["expected"])}
    if args.fetch_source or args.source_pdf:
        report["source_replay"] = check_source(args.source_pdf, args.fetch_source,
                                               load("data/pins.json"), data["expected"])
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
