#! /bin/bash

# This script computes the total verification time from log files
set -e

# check if the directory argument is provided
if [ -z "$1" ]; then
  echo "Usage: $0 <directory>"
  exit 1
fi

DIR=$(realpath "$1")

total=0

for f in "$DIR"/*.time; do
    [ -f "$f" ] || continue # skip if no .time files

    # each file contains a GNU time format string like:
    # [hours]:minutes:seconds.fraction
    time_str=$(cat "$f")

    if [[ "$time_str" =~ ^([0-9]+):([0-9]+\.[0-9]+)$ ]]; then
        min=${BASH_REMATCH[1]}
        sec=${BASH_REMATCH[2]}
        total=$(echo "$total + $min * 60 + $sec" | bc)
    elif [[ "$time_str" =~ ^([0-9]+):([0-9]+):([0-9]+\.[0-9]+)$ ]]; then
        hour=${BASH_REMATCH[1]}
        min=${BASH_REMATCH[2]}
        sec=${BASH_REMATCH[3]}
        total=$(echo "$total + $hour * 3600 + $min * 60 + $sec" | bc)
    else
        echo "Unrecognized time format in file $f: $time_str"
        exit 1
    fi
done

TOTAL_MIN=$(echo "$total/60" | bc)
TOTAL_SEC=$(echo "$total%60" | bc)

echo "Total verification time in minutes for $DIR: $TOTAL_MIN minutes $TOTAL_SEC seconds"