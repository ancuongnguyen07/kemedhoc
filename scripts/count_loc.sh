#! /bin/bash

# This script counts the lines of code in F* (.fst, .fsti) files
# and prints the total count. Note that this will skip all comments
# which is indicated by `//` and `(**)` and blank lines.

set -e

# Check if the directory argument is provided
if [ -z "$1" ]; then
  echo "Usage: $0 <directory>"
  exit 1
fi

ABS_DIR=$(realpath "$1")
TOTAL=$(cloc --force-lang="F#,fst" --force-lang="F#,fsti" --include-ext="fst,fsti" $ABS_DIR | grep SUM | awk '{print $5}')

echo "Total lines of code in F* (.fst, .fsti) files in $ABS_DIR: $TOTAL"
