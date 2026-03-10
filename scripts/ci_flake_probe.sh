#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

if [[ "$#" -lt 2 ]]; then
  echo "usage: $0 <probe-id> [attempts>=2] <command...>" >&2
  exit 2
fi

probe_id="$1"
shift 1

attempts="${CI_FLAKE_PROBE_ATTEMPTS:-3}"
if [[ "$#" -gt 0 && "$1" =~ ^[0-9]+$ ]]; then
  attempts="$1"
  shift 1
fi

if [[ "$#" -eq 0 ]]; then
  echo "usage: $0 <probe-id> [attempts>=2] <command...>" >&2
  exit 2
fi

if [[ "$attempts" -lt 2 ]]; then
  echo "attempt count must be >=2" >&2
  exit 2
fi

artifact_dir="${CI_TELEMETRY_ARTIFACT_DIR:-.ci-artifacts/telemetry}"
mkdir -p "${artifact_dir}"
log_path="${artifact_dir}/flake_probe.jsonl"

all_same=1
first_exit=""

for attempt in $(seq 1 "$attempts"); do
  start_epoch="$(date -u +%s)"
  start_iso="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

  set +e
  "$@"
  exit_code="$?"
  set -e

  end_epoch="$(date -u +%s)"
  end_iso="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  duration_s="$((end_epoch - start_epoch))"

  command_json="$(printf '%s\n' "$*" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read().rstrip("\n")))')"
  printf '{"probe_id":"%s","attempt":%s,"command":%s,"start":"%s","end":"%s","duration_seconds":%s,"exit_code":%s}\n' \
    "$probe_id" "$attempt" "$command_json" "$start_iso" "$end_iso" "$duration_s" "$exit_code" >> "$log_path"

  if [[ -z "$first_exit" ]]; then
    first_exit="$exit_code"
  elif [[ "$exit_code" -ne "$first_exit" ]]; then
    all_same=0
  fi

done

summary_path="${artifact_dir}/flake_summary.txt"
if [[ "$all_same" -eq 1 ]]; then
  echo "${probe_id}: stable (${attempts} attempts, exit=${first_exit})" >> "$summary_path"
else
  echo "${probe_id}: flaky signal detected (${attempts} attempts, mixed exit codes)" >> "$summary_path"
fi

if [[ "$first_exit" -ne 0 ]]; then
  echo "[CI-TELEMETRY] probe=${probe_id} initial attempt failed with exit=${first_exit}" >&2
  exit "$first_exit"
fi
