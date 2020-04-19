#!/bin/bash
set -o pipefail -o noclobber -o nounset

# Defaults
SATISFIABLE=10
UNSATISFIABLE=20
BINARY=btwl
DIFFICULTY=easy
TIMEOUT=30s
SEED_ARG=
PARAMS_ARG=
LABEL_ARG=
VERIFY=0

# Process any overrides from command-line flags.
while getopts ":b:d:l:p:t:s:v" opt; do
    case $opt in
        b)
            BINARY="${OPTARG}"
            ;;
        d)
            DIFFICULTY="${OPTARG}"
            ;;
        l)
            LABEL_ARG="${OPTARG}"
            ;;
        p)
            PARAMS_ARG="-p${OPTARG}"
            ;;
        s)
            SEED_ARG="-s${OPTARG}"
            ;;
        t)
            TIMEOUT="${OPTARG}"
            ;;
        v)
            VERIFY=1
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
if [[ "$?" != 0 ]]; then exit "$?"; fi

LABEL="label:${DIFFICULTY}"
NSUCCESS=0
NFAILURE=0
NTIMEOUT=0

start=`date +%s`

if [[ satisfiable == "${LABEL_ARG}"* ]]; then
    VERIFY_BIN=
    [ "${VERIFY}" -eq "1" ] && VERIFY_BIN="script/verify_sat.py"
    echo "Testing label:satisfiable, ${LABEL}: ${VERIFY_BIN}"
    for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:satisfiable'); do
        printf "${filename} "
        output="$(timeout ${TIMEOUT} ${VERIFY_BIN} ${BINARY} ${SEED_ARG} ${PARAMS_ARG} ${filename} 1>/dev/null 2>&1)"
        result="$?"
        if [ "${VERIFY}" -eq "1" ] && [ "$result" -eq "0" ]; then
            printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
            ((NSUCCESS++))
        elif [ "$result" -eq "124" ]; then
            printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
            ((NTIMEOUT++))
        elif [ "$result" -eq "$SATISFIABLE" ]; then
            printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
            ((NSUCCESS++))
        else
            printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
            ((NFAILURE++))
        fi
    done
    echo ""
fi

if [[ unsatisfiable == "${LABEL_ARG}"* ]]; then
    VERIFY_BIN=
    PROOF_ARG=
    if [ "${VERIFY}" -eq "1" ]; then
        VERIFY_BIN="script/verify_unsat.py"
        PROOF_ARG="-d/tmp/proof"
    fi
    echo "Testing label:unsatisfiable, ${LABEL}:"
    for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:unsatisfiable'); do
        printf "${filename} "
        output="$(timeout ${TIMEOUT} ${VERIFY_BIN} ${BINARY} ${SEED_ARG} ${PROOF_ARG} ${PARAMS_ARG} ${filename} 1>/dev/null 2>&1)"
        result="$?"
        if [ "${VERIFY}" -eq "1" ] && [ "$result" -eq "0" ]; then
            printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
            ((NSUCCESS++))
        elif [ "$result" -eq "124" ]; then
            printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
            ((NTIMEOUT++))
        elif [ "$result" -eq "$UNSATISFIABLE" ]; then
            printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
            ((NSUCCESS++))
        else
            printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
            ((NFAILURE++))
        fi
    done
    echo ""
fi

end=`date +%s`
runtime=$((end-start))

echo "${NSUCCESS} succeeded, ${NFAILURE} failed, ${NTIMEOUT} timed out in ${runtime} seconds."
