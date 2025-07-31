#!/bin/bash

set -e

# Constants
PV_DIR="proverif-models"

# Flags
all_spthy_flag=''
FILE_NAME=''
MODEL_FILES=lake*.spthy

print_help() {
    echo "Usage: -a for all .spthy files, specify a particular file with -f"
}

run_tamarin_prover() {
    local input_file="$1"
    local output_file="$PV_DIR/${input_file%.spthy}.pv"
    echo "Processing: $input_file"
    # Currently some attack scenrios, such as -D=NonRepudiation
    # -D=SanityChecks -D=WeakestSignature or their combination does not work due to
    # low memory of the machine. The process being killed during analysis.
    # If you want to run process for anonymity check, please use the following pre-processors
    # -D= diffEquiv -m=proverifequiv
    tamarin-prover -D=LeakSessionKey -D=LeakShare -m=proverif "$input_file" > "$output_file"
    echo "Done!: $input_file"
}

while getopts 'af:' flag; do
    case "${flag}" in
        a) all_spthy_flag='true';;
        f) FILE_NAME="${OPTARG}";;
        *)  print_help
            exit 1;;
    esac
done

# Ensure output directory exists
mkdir -p "$PV_DIR"

if [ "$all_spthy_flag" = 'true' ]; then
    for file in $MODEL_FILES; do
        [ -e "$file" ] || continue  # Skip if no files match
        run_tamarin_prover "$file"
    done
else
    if [ -z "$FILE_NAME" ]; then
        echo "Error: No file specified and -a flag not set."
        print_help
        exit 1
    fi
    
    if [ ! -f "$FILE_NAME" ]; then
        echo "Error: File '$FILE_NAME' not found."
        exit 1
    fi
    
    run_tamarin_prover "$FILE_NAME"
fi

echo "All steps have been done successfully!"
