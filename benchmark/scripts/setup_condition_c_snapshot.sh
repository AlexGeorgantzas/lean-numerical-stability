#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

# shellcheck source=benchmark/scripts/shared_lake_packages.sh
source "${script_dir}/shared_lake_packages.sh"

snapshot_dir="$(benchmark_condition_c_snapshot_dir "${repo_root}")"

make_tree_writable_no_follow() {
  local path="$1"
  if [[ -d "${path}" ]]; then
    find "${path}" -type d -exec chmod u+w {} +
    find "${path}" -type f -exec chmod u+w {} +
  fi
}

make_tree_readonly_no_follow() {
  local path="$1"
  find "${path}" -type f -exec chmod a-w {} +
  find "${path}" -type d -exec chmod a-w {} +
}

if [[ -f "${snapshot_dir}/.benchmark_condition_c_snapshot.md" ]]; then
  echo "Condition C snapshot already exists:"
  echo "  ${snapshot_dir}"
  exit 0
fi

benchmark_require_free_space "${snapshot_dir}" "${BENCHMARK_MIN_FREE_GB:-8}"

if [[ -e "${snapshot_dir}" ]]; then
  make_tree_writable_no_follow "${snapshot_dir}"
  rm -rf "${snapshot_dir}"
fi

tmp_snapshot="$(mktemp -d "${TMPDIR:-/tmp}/lean-fp-condition-c-snapshot.XXXXXX")"
cleanup_tmp_snapshot() {
  if [[ -d "${tmp_snapshot}" ]]; then
    make_tree_writable_no_follow "${tmp_snapshot}"
    rm -rf "${tmp_snapshot}"
  fi
}
trap cleanup_tmp_snapshot EXIT

copy_if_exists() {
  local source="$1"
  local target="$2"
  if [[ -e "${source}" ]]; then
    cp -R "${source}" "${target}"
  fi
}

copy_if_exists "${repo_root}/LeanFpAnalysis.lean" "${tmp_snapshot}/LeanFpAnalysis.lean"
copy_if_exists "${repo_root}/LeanFpAnalysis" "${tmp_snapshot}/LeanFpAnalysis"
copy_if_exists "${repo_root}/Main.lean" "${tmp_snapshot}/Main.lean"
copy_if_exists "${repo_root}/README.md" "${tmp_snapshot}/README.md"
copy_if_exists "${repo_root}/docs" "${tmp_snapshot}/docs"
copy_if_exists "${repo_root}/examples" "${tmp_snapshot}/examples"
copy_if_exists "${repo_root}/lakefile.toml" "${tmp_snapshot}/lakefile.toml"
copy_if_exists "${repo_root}/lake-manifest.json" "${tmp_snapshot}/lake-manifest.json"
copy_if_exists "${repo_root}/lean-toolchain" "${tmp_snapshot}/lean-toolchain"

benchmark_link_shared_lake_packages "${repo_root}" "${tmp_snapshot}"

echo "building Condition C snapshot:"
echo "  ${snapshot_dir}"
(cd "${tmp_snapshot}" && lake build LeanFpAnalysis)

(
  cd "${tmp_snapshot}"
  find \
    LeanFpAnalysis.lean \
    LeanFpAnalysis \
    Main.lean \
    README.md \
    docs \
    examples \
    lakefile.toml \
    lake-manifest.json \
    lean-toolchain \
    -type f -print0 2>/dev/null |
    sort -z |
    xargs -0 shasum -a 256 > .benchmark_condition_c_public_files.sha256
)

commit="$(git -C "${repo_root}" rev-parse HEAD)"
branch="$(git -C "${repo_root}" branch --show-current)"
timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

cat > "${tmp_snapshot}/.benchmark_condition_c_snapshot.md" <<EOF
# Condition C Snapshot

- source_branch: \`${branch}\`
- source_commit: \`${commit}\`
- created_at_utc: \`${timestamp}\`
- public_id: \`$(benchmark_condition_c_public_id "${repo_root}")\`
- shared_lake_packages: \`$(benchmark_shared_lake_packages_dir "${repo_root}")\`
EOF

mkdir -p "$(dirname "${snapshot_dir}")"
mv "${tmp_snapshot}" "${snapshot_dir}"
make_tree_readonly_no_follow "${snapshot_dir}"
trap - EXIT

echo "Condition C snapshot ready:"
echo "  ${snapshot_dir}"
