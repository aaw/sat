#!/bin/bash
set -o pipefail -o noclobber -o nounset

# Defaults
SATISFIABLE=10
UNSATISFIABLE=20
CONTROL_BINARY=cdcl
EXPERIMENT_BINARY=look
DIFFICULTY=easy
TIMEOUT=30s
SEED_ARG=
EXPERIMENT_PARAMS_ARG=

# Process any overrides from command-line flags.
while getopts ":b:c:d:p:t:s:" opt; do
    case $opt in
        b)
            EXPERIMENT_BINARY="${OPTARG}"
            ;;
        c)
            CONTROL_BINARY="${OPTARG}"
            ;;
        d)
            DIFFICULTY="${OPTARG}"
            ;;
        p)
            EXPERIMENT_PARAMS_ARG="-p${OPTARG}"
            ;;
        s)
            SEED_ARG="${OPTARG}"
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

case $DIFFICULTY in
    easy)
        ARGS="25 50 3"
        ;;
    medium)
        ARGS="200 800 3"
        ;;
    hard)
        ARGS="1000 3500 3"
        ;;
    :)
        echo "Unknown difficulty $DIFFICULTY selected."
        exit 1
        ;;
esac

if [ -n "$SEED_ARG" ]; then
    echo "Setting seed = ${SEED_ARG}"
    RANDOM="${SEED_ARG}"
fi

CONTROL_BINARY="bin/${CONTROL_BINARY}"
EXPERIMENT_BINARY="bin/${EXPERIMENT_BINARY}"
echo "Testing binary ${CONTROL_BINARY} using ${EXPERIMENT_BINARY} as control."

make ${CONTROL_BINARY}
if [[ "$?" != 0 ]]; then exit "$?"; fi
make ${EXPERIMENT_BINARY}
if [[ "$?" != 0 ]]; then exit "$?"; fi

LABEL="label:${DIFFICULTY}"
NSUCCESS=0
NFAILURE=0
NTIMEOUT=0

start=`date +%s`

echo "Testing ${DIFFICULTY} examples:"
for i in {1..20}; do
    seed="${RANDOM}"
    printf "rand ${ARGS} ${seed} "
    ./gen/rand.py ${ARGS} ${seed} >| /tmp/test.cnf
    control_start=`date +%s%N`
    control_output="$(timeout ${TIMEOUT} ${CONTROL_BINARY} /tmp/test.cnf 1>/dev/null 2>&1)"
    control_result="$?"
    control_end=`date +%s%N`
    control_time=$((control_end-control_start))
    experiment_start=`date +%s%N`
    experiment_output="$(timeout ${TIMEOUT} ${EXPERIMENT_BINARY} ${EXPERIMENT_PARAMS_ARG} /tmp/test.cnf 1>/dev/null 2>&1)"
    experiment_result="$?"
    experiment_end=`date +%s%N`
    experiment_time=$((experiment_end-experiment_start))
    total_time=$((experiment_time-control_time))
    total_secs=$(bc <<<"scale=2;${total_time}/1000000000.0")
    if [[ "$control_result" -eq 124 ]] && [[ "$experiment_result" -eq 124 ]]; then
        printf $'\u001b[31m\u23f1\u001b[0m\n' # Red stopwatch
        ((NTIMEOUT++))
    elif [[ "$control_result" -eq 124 ]]; then
        printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
        ((NTIMEOUT++))
    elif [[ "$experiment_result" -eq 124 ]]; then
        printf $'\u001b[32m\u23f1\u001b[0m\n' # Green stopwatch
        ((NTIMEOUT++))
    elif [[ "$control_result" -eq "$SATISFIABLE" ]] && [[ "$experiment_result" -eq "$SATISFIABLE" ]]; then
        printf $'\u001b[32m\u2714\u001b[0m'" (${total_secs}s)\n" # Green check
        ((NSUCCESS++))
    elif [[ "$control_result" -eq "$UNSATISFIABLE" ]] && [[ "$experiment_result" -eq "$UNSATISFIABLE" ]]; then
        printf $'\u001b[33m\u2714\u001b[0m'" (${total_secs}s)\n" # Yellow check
        ((NSUCCESS++))
    else
        printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
        ((NFAILURE++))
    fi
done
echo ""

end=`date +%s`
runtime=$((end-start))

echo "${NSUCCESS} succeeded, ${NFAILURE} failed, ${NTIMEOUT} timed out in ${runtime} seconds."
