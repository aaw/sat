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
NSUCCESS=0
NFAILURE=0
NTIMEOUT=0

echo "Testing label:satisfiable, ${LABEL}:"
for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:satisfiable'); do
    printf "${filename} "
    output="$(timeout ${TIMEOUT} ${BINARY} ${filename} 1>/dev/null 2>&1)"
    result="$?"
    if [ "$result" -eq "124" ]; then
        printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
        ((NTIMEOUT++))
    elif [ "$result" -eq "0" ]; then
        printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
        ((NSUCCESS++))
    else
        printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
        ((NFAILURE))
    fi
done
echo ""

echo "Testing label:unsatisfiable, ${LABEL}:"
for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:unsatisfiable'); do
    printf "${filename} "
    output="$(timeout ${TIMEOUT} ${BINARY} ${filename} 1>/dev/null 2>&1)"
    result="$?"
    if [ "$result" -eq "124" ]; then
        printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
        ((NTIMEOUT++))
    elif [ "$result" -eq "0" ]; then
        printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
        ((NFAILURE++))
    else
        printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
        ((NSUCCESS++))
    fi
done
echo ""

echo "${NSUCCESS} succeeded, ${NFAILURE} failed, ${NTIMEOUT} timed out."