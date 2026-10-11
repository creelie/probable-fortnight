#!/usr/bin/env bash
# get_tools.sh -- build the pinned SAT solver and proof trimmer into build/tools.
#   CaDiCaL 3.0.1   https://github.com/arminbiere/cadical   commit c60730422e758ef1cebe7aeddf2dda31c996bf04
#   lrat-trim 0.2.0 https://github.com/arminbiere/lrat-trim commit b30f400f4ee5c32b77ee566a7c006081b521534f
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
T="$ROOT/build/tools"
mkdir -p "$T"
fetch() {  # repo commit dir
  if [ ! -d "$T/$3" ]; then
    git clone -q "$1" "$T/$3"
    git -C "$T/$3" checkout -q "$2"
  fi
}
fetch https://github.com/arminbiere/cadical.git c60730422e758ef1cebe7aeddf2dda31c996bf04 cadical
fetch https://github.com/arminbiere/lrat-trim.git b30f400f4ee5c32b77ee566a7c006081b521534f lrat-trim
(cd "$T/cadical" && [ -x build/cadical ] || { ./configure > /dev/null && make -j"$(nproc)" > /dev/null; })
(cd "$T/lrat-trim" && [ -x lrat-trim ] || { ./configure > /dev/null && make > /dev/null; })
"$T/cadical/build/cadical" --version
"$T/lrat-trim/lrat-trim" --version
