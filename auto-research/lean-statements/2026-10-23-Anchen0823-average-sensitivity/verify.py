"""Reproduce statement sanity checks; standard library, no network by default."""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
import os
from pathlib import Path
import subprocess
import tempfile

PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]
PROOF_COMMIT = "cb8c10538e613329be16f9a949d0d75a4c7c67f0"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def integrity():
    manifest = read_json(PACKAGE / "MANIFEST.json")
    require(manifest["algorithm"] == "sha256", "manifest algorithm")
    files = {p.relative_to(PACKAGE).as_posix() for p in PACKAGE.rglob("*")
             if p.is_file() and p.name != "MANIFEST.json"}
    require(files == set(manifest["sha256"]), "package file inventory changed")
    for base, hashes in [(PACKAGE, manifest["sha256"]),
                         (ROOT, read_json(PACKAGE / "data/source-hashes.json"))]:
        for name, digest in hashes.items():
            path = base / name
            require(not path.is_symlink(), f"symlink: {name}")
            require(sha256(path.read_bytes()).hexdigest() == digest, f"hash: {name}")
    model = ROOT / "challenges/average-sensitivity"
    provenance = read_json(model / "provenance.json")
    require(sha256((model / provenance["local_path"]).read_bytes()).hexdigest()
            == provenance["sha256"], "upstream model provenance")
    pins = read_json(ROOT / "profiles/anthropic-lake-manifest.json")
    mathlib = next(p for p in pins["packages"] if p["name"] == "mathlib")
    require(mathlib["rev"] == provenance["mathlib"], "Mathlib pin mismatch")


def evaluate(polynomial, vertex):
    return sum(c * monomial_value(exponents, vertex)
               for exponents, c in polynomial.items())


def monomial_value(exponents, vertex):
    value = 1
    for x, power in zip(vertex, exponents):
        value *= x ** power
    return value


def threshold(value):
    return 1 if value >= 0 else -1


def sensitivity(n, polynomial):
    vertices = list(product((-1, 1), repeat=n))
    values = {x: threshold(evaluate(polynomial, x)) for x in vertices}
    counts = []
    for i in range(n):
        counts.append(sum(values[x] != values[x[:i] + (-x[i],) + x[i + 1:]]
                          for x in vertices))
    return Fraction(sum(counts), 2 ** n)


def holds(as_value, coefficient, n, d):
    # Both sides are nonnegative. Squaring avoids any floating-point sqrt.
    require(as_value >= 0 and coefficient >= 0 and 1 <= d <= n, "invalid domain")
    return as_value ** 2 <= coefficient ** 2 * d ** 2 * n


def finite_checks():
    require(threshold(0) == 1, "sign at zero")
    require(sensitivity(1, {(1,): 1}) == 1, "dictator normalization")
    require(not holds(Fraction(1), Fraction(0), 1, 1), "wrong bound zero accepted")
    require(not holds(Fraction(1), Fraction(999, 1000), 1, 1), "wrong bound accepted")
    require(holds(Fraction(1), Fraction(1), 1, 1), "sharp one-dimensional bound")
    require(sensitivity(1, {(1,): 1, (0,): 1}) == 0, "zero tie convention")
    count = 0
    nonmultilinear = 0
    for n in range(1, 5):
        require(sensitivity(n, {}) == 0, "zero polynomial")
        require(sensitivity(n, {(0,) * n: -1}) == 0, "negative constant")
        require(sensitivity(n, {(1,) * n: 1}) == n, "parity normalization")
        # Exhaust all ternary-coefficient multilinear polynomials for n <= 3.
        if n <= 3:
            monomials = list(product((0, 1), repeat=n))
            for coefficients in product((-1, 0, 1), repeat=len(monomials)):
                polynomial = {m: c for m, c in zip(monomials, coefficients) if c}
                degree = max((sum(m) for m in polynomial), default=0)
                value = sensitivity(n, polynomial)
                require(0 <= value <= n, "sensitivity outside [0,n]")
                for d in range(max(1, degree), n + 1):
                    for c in (Fraction(8), Fraction(1881, 500)):
                        require(holds(value, c, n, d), "finite bound violation")
                count += 1
        # General polynomials: square/cube terms, including roots on the cube.
        for power in range(2, n + 1):
            for constant in (-1, 0, 1):
                for coefficient in (-1, 1):
                    exponents = (power,) + (0,) * (n - 1)
                    polynomial = {exponents: coefficient, (0,) * n: constant}
                    reduced = {}
                    for m, c in polynomial.items():
                        key = tuple(e % 2 for e in m)
                        reduced[key] = reduced.get(key, 0) + c
                    for vertex in product((-1, 1), repeat=n):
                        require(evaluate(polynomial, vertex) == evaluate(reduced, vertex),
                                "parity reduction changed cube values")
                    value = sensitivity(n, polynomial)
                    require(holds(value, Fraction(1881, 500), n, power), "power example")
                    nonmultilinear += 1
    # AS <= n alone does not imply the target, e.g. d=1, n=65, C=8.
    require(not holds(Fraction(65), Fraction(8), 65, 1), "trivial bound diagnostic")
    return {"multilinear_polynomials": count, "nonmultilinear_polynomials": nonmultilinear,
            "wrong_coefficients_rejected": ["0", "999/1000"],
            "dictator_average_sensitivity": "1", "sign_at_zero": 1}


def lean_checks(project):
    """Optional full positive check in the already pinned public proof checkout."""
    require(os.environ.get("GITHUB_ACTIONS") == "true", "Lean runs only on GitHub Actions")
    project = project.resolve()
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
    require(head == PROOF_COMMIT, "wrong proof repository commit")
    source = (project / "Submission.lean").read_text(encoding="utf-8")
    challenge = ROOT / "challenges/average-sensitivity"
    # Match actual target and full model bodies, not just a theorem name.
    for path, namespace, ending in [
        (challenge / "Statement.lean", "namespace BigOSpeedrun.AverageSensitivity",
         "end BigOSpeedrun.AverageSensitivity"),
        (challenge / "OAI/Combinatorics/GotsmanLinial/Model.lean", "namespace OAI", "end OAI")]:
        body = path.read_text(encoding="utf-8")
        body = body[body.index(namespace):body.index(ending) + len(ending)]
        require(body in source, f"public proof differs from proposed definitions: {path.name}")
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-o", "Submission.olean",
                    "Submission.lean"], cwd=project, check=True)
    # Compile the package's bridge after the standalone proof and its axiom guard.
    with tempfile.TemporaryDirectory(prefix="average-sensitivity-") as temporary:
        check = Path(temporary) / "BaselineCheck.lean"
        check.write_bytes((PACKAGE / "code/BaselineCheck.lean").read_bytes())
        env = dict(os.environ)
        env["LEAN_PATH"] = str(project) + os.pathsep + env.get("LEAN_PATH", "")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", str(check)],
                       cwd=project, env=env, check=True)
    print("PASS: full public proof, exact model/target bodies, coefficient-eight baseline, allowed axioms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-project", type=Path,
                        help="GitHub Actions only: prepared public proof checkout at the pinned commit")
    args = parser.parse_args()
    integrity()
    actual = finite_checks()
    require(actual == read_json(PACKAGE / "data/expected.json"), "unexpected finite results")
    print("PASS: package inventory, SHA-256, frozen model, challenge and dependency pins")
    print(json.dumps(actual, sort_keys=True))
    print("PASS: exact finite sanity checks; these are not a universal proof or a Comparator receipt")
    if args.lean_project:
        lean_checks(args.lean_project)


if __name__ == "__main__":
    main()
