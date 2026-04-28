#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

# shellcheck source=benchmark/scripts/shared_lake_packages.sh
source "${script_dir}/shared_lake_packages.sh"

cache_dir="$(benchmark_shared_lake_packages_dir "${repo_root}")"
repo_packages="${repo_root}/.lake/packages"

mkdir -p "$(dirname "${cache_dir}")"

if [[ -d "${cache_dir}/mathlib" ]]; then
  echo "shared Lake package cache already exists:"
  echo "  ${cache_dir}"
elif [[ -L "${repo_packages}" ]]; then
  target="$(readlink "${repo_packages}")"
  if [[ -d "${target}/mathlib" ]]; then
    echo "repo already points at shared Lake package cache:"
    echo "  ${target}"
    cache_dir="${target}"
  else
    echo "broken .lake/packages symlink: ${repo_packages} -> ${target}" >&2
    exit 1
  fi
elif [[ -d "${repo_packages}/mathlib" ]]; then
  echo "moving existing third-party Lake packages into shared cache:"
  echo "  from: ${repo_packages}"
  echo "  to:   ${cache_dir}"
  mv "${repo_packages}" "${cache_dir}"
else
  echo "cannot initialize shared cache: no existing ${repo_packages}/mathlib found" >&2
  echo "build the project once, or set BENCHMARK_LAKE_PACKAGES_CACHE to an existing package cache" >&2
  exit 1
fi

mkdir -p "${repo_root}/.lake"
if [[ -L "${repo_packages}" ]]; then
  rm "${repo_packages}"
elif [[ -e "${repo_packages}" ]]; then
  echo "refusing to replace non-symlink package directory: ${repo_packages}" >&2
  exit 1
fi

ln -s "${cache_dir}" "${repo_packages}"

echo "repo .lake/packages now points at:"
echo "  ${cache_dir}"
