#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
cd $SCRIPT_DIR

profile() {
    noir-profiler gates \
        --artifact-path ./simple/target/simple_regex.json \
        --backend-path $BACKEND_BINARY_PATH \
        --output .
    mv main::gates.svg flamegraph.svg
}

BACKEND_BINARY_PATH=$(which bb)

profile

cd - > /dev/null