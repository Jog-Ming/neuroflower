#!/usr/bin/env bash
# The experimental pipeline's entry point.
#
#   ./nf versions | download <version> | decompile <version> | score <version> | class <version> <Class>
#   ./nf tree <version> | clean [--trees|--downloads|--all] | cache
#
# Everything the pipeline writes lives under .dev/ and is git-ignored. The devtools jar is rebuilt
# only when its sources or build file are newer than it; the JDK must be 21 or newer because the
# verifier compiles Minecraft classes at the target's release.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
jar="$root/devtools/build/libs/devtools-all.jar"

if [ ! -f "$jar" ] || [ -n "$(find "$root/devtools/src" "$root/devtools/build.gradle" -newer "$jar" -print -quit 2>/dev/null)" ]; then
  (cd "$root" && ./gradlew :devtools:shadowJar -q)
fi

jdk="${NF_JDK:-$(command -v java)}"
major="$("$jdk" -version 2>&1 | sed -n 's/.*version "\([0-9][0-9]*\).*/\1/p' | head -1)"
if [ -z "$major" ] || [ "$major" -lt 21 ]; then
  echo "nf: need JDK 21 or newer to run the pipeline (found $jdk); set NF_JDK" >&2
  exit 2
fi

NF_ROOT="$root" exec "$jdk" -jar "$jar" "$@"
