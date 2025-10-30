#!/bin/bash

set -e

PV_FILE=""
SUFFIX=""
CPP_FLAGS=()

print_help() {
    echo "Usage: $0 -f <file.pv> [-D DEF]"
    echo "  -f <file.pv>    Specify the ProVerif file to process."
    echo "  -D <DEF>        Define a macro for the preprocessor. Pick ONLY one among [Anonymity, Model, ReflectionSimul]."
}

run_proverif() {
    local file_name="$1"
    local BASE_NAME=${file_name%.pv}
    local ATK_GRAPH_DIR="attack-graphs/$BASE_NAME"
    local processed_file_name="${BASE_NAME}${SUFFIX}"

    echo "CPP preprocessing..."
    cpp -P -traditional-cpp "${CPP_FLAGS[@]}" "$file_name" > "${processed_file_name}.pv" 2> /dev/null
    echo "Preprocessing done!"

    echo "Running ProVerif..."
    mkdir -p "$ATK_GRAPH_DIR"
    time (proverif -graph "$ATK_GRAPH_DIR" "${processed_file_name}.pv") > "${processed_file_name}".log
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        -f) PV_FILE="$2"; shift 2;;
        -D)
            CPP_FLAGS+=("-D$2")
            SUFFIX="-$2"  # Set the suffix to the last -D value
            shift 2;;
        *) print_help; exit 1;;
    esac
done

if [[ -z "$PV_FILE" ]]; then
    echo "Error: no input file specififed"
    print_help
    exit 1
fi

run_proverif "$PV_FILE"
echo "All steps have been done successfully!"