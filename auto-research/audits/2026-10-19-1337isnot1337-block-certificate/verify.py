"""Replay the finite certificate; this does not prove the Boolean construction."""

import hashlib
import json
import math
from pathlib import Path
import stat
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def read_json(name):
    return json.loads((HERE / name).read_text())


def check_files():
    manifest = read_json("MANIFEST.json")
    require(manifest["algorithm"] == "sha256", "manifest algorithm")
    files = {}
    for path in HERE.rglob("*"):
        require(not path.is_symlink(), "symlink: " + str(path))
        if path.is_dir():
            continue
        require(stat.S_ISREG(path.stat().st_mode), "nonregular file")
        require(not path.stat().st_mode & 0o111, "executable: " + str(path))
        if path != HERE / "MANIFEST.json":
            files[path.relative_to(HERE).as_posix()] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
    require(files == manifest["sha256"], "package file inventory or hash")
    pins = read_json("data/source-pins.json")["files"]
    for local, suffix in [
        ("verify_certificate.py", "checkers/verify_certificate.py"),
        ("LICENSE", "/LICENSE"),
        ("NOTICE", "/NOTICE"),
    ]:
        pin = next(
            item for item in pins
            if (item["embedded_path"] or item["url"]).endswith(suffix)
        )
        data = (HERE / "upstream" / local).read_bytes()
        require(len(data) == pin["bytes"], "source size: " + local)
        require(hashlib.sha256(data).hexdigest() == pin["sha256"],
                "source hash: " + local)


def replay(parameters, wrong_gate_index=False):
    """Use equation (12)'s one-based indices rather than upstream's lists."""
    depth = parameters["depth"]
    size = parameters["block_size"]
    initial = parameters["initial_blocks"]
    schedule = parameters["schedule"]
    require(len(schedule) == depth, "schedule length")
    zero = {q: size - q for q in range(1, depth + 2)}
    one = {q: size * initial - depth - 1 + q for q in zero}
    joint_zero = joint_one = 0
    vertex_counts = []
    for level, exponent in enumerate(schedule, 1):
        outdegree = 2 ** exponent
        threshold = exponent + 6
        vertices = 2 * outdegree + 1
        require(vertices ** threshold * 4 ** threshold
                < 4 ** math.comb(threshold, 2), "label union bound")
        vertex_counts.append(vertices)
        target = depth + 2 - level
        require(set(zero) == set(range(1, target + 1)), "child indices")
        parent_zero, parent_one = {}, {}
        for q in range(1, target):
            gate = q if wrong_gate_index else target - q
            parent_zero[q] = (threshold - 1) * zero[target] + max(
                one[gate] + joint_one, 3 * joint_one)
            parent_one[q] = outdegree * zero[gate] + 4 * one[target]
        parent_joint_zero = (threshold - 1) * zero[target] + 3 * joint_one
        parent_joint_one = outdegree * joint_zero + 4 * one[target]
        zero, one = parent_zero, parent_one
        joint_zero, joint_one = parent_joint_zero, parent_joint_one
    blocks = parameters["copies"] * initial * math.prod(vertex_counts)
    return zero[1], one[1], blocks


def check_author_replay():
    expected = "PASS: exact seed and strict exponent inequalities"
    source_path = HERE / "upstream/verify_certificate.py"
    for flags in ([], ["-O"]):
        result = subprocess.run(
            [sys.executable, "-I", "-B", *flags, str(source_path)],
            capture_output=True, text=True, check=True)
        require(result.stdout.strip() == expected, "author replay output")
    source = source_path.read_text()
    original = 'require(block_count == expected_blocks, "block count")'
    require(source.count(original) == 1, "mutation anchor")
    changed = source.replace(original, original.replace(
        "expected_blocks,", "expected_blocks + 1,"))
    with tempfile.TemporaryDirectory(prefix="block-certificate-") as folder:
        mutation = Path(folder) / "wrong_block_count.py"
        mutation.write_text(changed)
        result = subprocess.run(
            [sys.executable, "-I", "-B", "-O", str(mutation)],
            capture_output=True, text=True)
    require(result.returncode != 0 and "ArithmeticError: block count" in result.stderr,
            "optimized author checker must reject a wrong block count")


def main():
    check_files()
    parameters = read_json("data/certificate.json")
    zero, sensitivity, blocks = replay(parameters)
    expected = tuple(int(parameters[key]) for key in [
        "expected_zero_profile", "expected_sensitivity_bound", "expected_block_count"])
    require((zero, sensitivity, blocks) == expected, "reported final values")
    require(1 < sensitivity < blocks, "positive logarithm and exponent direction")
    require(99 * zero <= sensitivity < 100 * zero, "OR balance boundary")
    require(blocks ** 187 > sensitivity ** 380, "paper exponent")
    require(380 * 10 ** 6 > 2032083 * 187, "paper decimal threshold")
    require(blocks ** 5000 > sensitivity ** 10161, "stronger numerical lower bound")
    require(blocks ** 1000 < sensitivity ** 2033, "numerical upper bound")
    require((100 * 2 ** 646) ** 187 < (9 * 2 ** 318) ** 380,
            "author's frozen comparison")
    require(replay(parameters, wrong_gate_index=True) != expected,
            "wrong gate index must change the reported final values")
    check_author_replay()
    print("PASS: 20 indexed recurrence stages and 20 label union bounds")
    print("PASS: author's checker in normal and optimized Python")
    print("PASS: B^187 > S^380 and 380/187 > 2.032083")
    print("PASS: 10161/5000 < log(B)/log(S) < 2033/1000 (integer checks)")
    print("PASS: wrong-index, 100-copy frozen-S, wrong-block, and 2.033 controls")
    print("SCOPE: finite certificate only; no all-input theorem or Lean verification")


if __name__ == "__main__":
    main()
