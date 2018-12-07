#!/bin/bash
set -o pipefail -o noclobber -o nounset

# Defaults
BINARY=btwl
DIFFICULTY=easy
TIMEOUT=30s

# Process any overrides from command-line flags.
while getopts ":b:d:t:" opt; do
    case $opt in
        b)
            BINARY="${OPTARG}"
            ;;
        d)
            DIFFICULTY="${OPTARG}"
            ;;
        t)
            TIMEOUT="${OPTARG}"
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

LABEL="label:${DIFFICULTY}"
echo "Testing label:satisfiable, ${LABEL}:"
for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:satisfiable'); do
    # TODO: turn next few lines into a function
    echo "${filename}"
    output="$(timeout ${TIMEOUT} ${BINARY} ${filename} 1>/dev/null 2>&1)"
    result="$?"
    if [ "$result" -eq "124" ]; then
        printf 'T'
    elif [ "$result" -eq "0" ]; then
        printf '.'
    else
        echo "${filename} should be satisifiable but ${BINARY} reports otherwise"
    fi
done
echo ""

echo "Testing label:unsatisfiable, ${LABEL}:"
for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:unsatisfiable'); do
    echo "${filename}"
    output="$(timeout ${TIMEOUT} ${BINARY} ${filename} 1>/dev/null 2>&1)"
    result="$?"
    if [ "$result" -eq "124" ]; then
        printf 'T'
    elif [ "$result" -eq "0" ]; then
        echo "${filename} should be unsatisifiable but ${BINARY} reports otherwise"
    else
        printf '.'
    fi
done
echo ""
