#!/usr/bin/env python3
"""Formal submission client for SAIR Lean Kernel Challenge.

Implements the checklist in results/LKC_2026-10-14_PASO-C_auditoria_checklist.md:
1. Verifies file size <= 1 MiB and expected SHA-256 prefix.
2. Fetches GET /submission-spec to confirm contractVersion.
3. Sends POST /api/public/v1/competitions/lean-kernel-challenge/submissions with
   {idempotencyKey, contractVersionAcknowledged, payload: {problem, text}}.
4. Queries GET /submissions/mine to verify the newly recorded submission.
"""
from __future__ import annotations

import hashlib
import json
import sys
import uuid
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lk_playground  # noqa: E402
from lk_playground import curl  # noqa: E402

COMP = "/api/public/v1/competitions/lean-kernel-challenge"
lk_playground.BASE = "https://api.sair.foundation"

EXPECTED_CONTRACT = "ddd9cae8db44a2ace1adea86e908263087aae499"


def submit_one(problem: str, file_path: Path, expected_sha_prefix: str) -> dict:
    raw_bytes = file_path.read_bytes()
    if len(raw_bytes) > 1048576:
        raise SystemExit(f"File too large: {len(raw_bytes)} > 1 MiB")
    sha = hashlib.sha256(raw_bytes).hexdigest()
    if not sha.startswith(expected_sha_prefix):
        raise SystemExit(
            f"SHA-256 mismatch for {file_path}: got {sha}, expected prefix {expected_sha_prefix}"
        )
    text = raw_bytes.decode("utf-8")

    spec = curl("GET", f"{COMP}/submission-spec")
    if not spec.get("ok"):
        raise SystemExit(f"GET /submission-spec failed: {spec}")
    cv = spec["data"]["contractVersion"]
    if cv != EXPECTED_CONTRACT:
        raise SystemExit(f"contractVersion changed: {cv} != {EXPECTED_CONTRACT}")

    idem = f"formal-{problem}-{sha[:12]}-{uuid.uuid4()}"
    body = {
        "idempotencyKey": idem,
        "contractVersionAcknowledged": cv,
        "payload": {
            "problem": problem,
            "text": text,
        },
    }
    resp = curl("POST", f"{COMP}/submissions", body)
    print(f"=== POST /submissions [{problem}] ({file_path}) ===")
    print(f"  sha256: {sha} ({len(raw_bytes)} B)")
    print("  response:", json.dumps(resp, indent=2))
    if not resp.get("ok"):
        raise SystemExit(f"POST /submissions failed for {problem}")
    return resp["data"]


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    targets = [
        ("ca-rule110", root / "candidates/ca-rule110-v5/Submission.lean", "16b9fd21fda4c86e"),
        ("primecount", root / "candidates/primecount-v2/Submission.lean", "1a1da51f05bb9252"),
        ("mertens", root / "candidates/mertens-v2/Submission.lean", "2c906a223e62d38f"),
        ("polydisc", root / "candidates/polydisc-v2/Submission.lean", "4464f8ef43403588"),
        ("sha256", root / "candidates/sha256-v3/Submission.lean", "20d958db51bb508b"),
        ("fib", root / "candidates/fib-v3/Submission.lean", "7c8ba7edfd1606f8"),
    ]
    for problem, path, sha_prefix in targets:
        submit_one(problem, path, sha_prefix)

    mine = curl("GET", f"{COMP}/submissions/mine")
    print("\n=== GET /submissions/mine ===")
    for item in mine.get("data", {}).get("items", []):
        print(
            f"  submissionId={item.get('submissionId')} "
            f"problem={item.get('problem'):12s} "
            f"status={item.get('status')} "
            f"sha256={item.get('rawUploadSha256')[:16]}... "
            f"createdAt={item.get('createdAt')}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
