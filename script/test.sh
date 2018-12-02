#!/bin/bash
set -o errexit -o pipefail -o noclobber -o nounset

# Defaults
BINARY=btwl

# Process any overrides from command-line flags.
while getopts ":b:" opt; do
    case $opt in
        b)
            BINARY="${OPTARG}"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
        :)
            echo "Option -$OPTARG requires an argument." >&2
            exit 1
            ;;
    esac
done

BINARY="bin/${BINARY}"
echo "Testing binary ${BINARY}"

make ${BINARY}

echo "Testing label:satisfiable, label:easy:"
for filename in $(grep -l 'label:easy' test/*.cnf | xargs grep -l 'label:satisfiable'); do
    if ! ${BINARY} ${filename} 1>/dev/null 2>&1; then
        echo ""
        echo "${filename} should be satisifiable but ${BINARY} reports otherwise"
    else
        printf '.'
    fi
done
echo ""

echo "Testing label:unsatisfiable, label:easy:"
for filename in $(grep -l 'label:easy' test/*.cnf | xargs grep -l 'label:unsatisfiable'); do
    if ${BINARY} ${filename} 1>/dev/null 2>&1; then
        echo ""
        echo "${filename} should be unsatisifiable but ${BINARY} reports otherwise"
    else
        printf '.'
    fi
done
echo ""
