#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -lt 2 ]]; then
  echo "usage: $0 <lane-name> <command...>" >&2
  exit 2
fi

lane="$1"
shift

artifact_dir="${CI_TELEMETRY_ARTIFACT_DIR:-.ci-artifacts/telemetry}"
mkdir -p "${artifact_dir}"
log_path="${artifact_dir}/timing.jsonl"

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

printf '{"lane":"%s","command":%s,"start":"%s","end":"%s","duration_seconds":%s,"exit_code":%s}\n' \
  "$lane" "$command_json" "$start_iso" "$end_iso" "$duration_s" "$exit_code" >> "$log_path"

if [[ "$exit_code" -ne 0 ]]; then
  echo "[CI-TELEMETRY] lane=${lane} command failed with exit=${exit_code}" >&2
  exit "$exit_code"
fi
