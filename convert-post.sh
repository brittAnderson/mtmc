#!/usr/bin/env bash
# convert-post.sh — convert an org post to markdown with citations baked in.
#
# Reads posts/org/<name>.org and writes posts/<name>.markdown, resolving
# [cite:@key] citations against the bibliography using the given CSL style.
# Run from the repository root:
#
#     ./convert-post.sh 2026-07-28-braitenberg
#
set -euo pipefail

# --- configuration ----------------------------------------------------------
BIB="/home/britt/gitRepos/masterBib/bayatt.bib"
CSL="$HOME/gitRepos/mtmc/chicago-fullnote-16th-edition.csl"
SRC_DIR="posts/org"
OUT_DIR="posts"

# --- argument handling -------------------------------------------------------
if [[ $# -ne 1 ]]; then
  echo "usage: $0 <post-name-without-extension>" >&2
  echo "example: $0 2026-07-28-braitenberg" >&2
  exit 1
fi

name="$1"
# Strip a trailing .org if the user tab-completed the filename.
name="${name%.org}"

src="${SRC_DIR}/${name}.org"
out="${OUT_DIR}/${name}.markdown"

# --- sanity checks -----------------------------------------------------------
if [[ ! -f "$src" ]]; then
  echo "error: source file not found: $src" >&2
  exit 1
fi
if [[ ! -f "$BIB" ]]; then
  echo "error: bibliography not found: $BIB" >&2
  exit 1
fi
if [[ ! -f "$CSL" ]]; then
  echo "error: CSL style not found: $CSL" >&2
  exit 1
fi

# --- conversion --------------------------------------------------------------
pandoc -s -f org -t markdown \
  --bibliography "$BIB" \
  --csl "$CSL" \
  --citeproc \
  "$src" \
  -o "$out"

echo "wrote $out"
