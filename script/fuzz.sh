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
CONTROL_SEED=
COUNT=20

# Process any overrides from command-line flags.
while getopts ":b:c:d:n:p:r:t:s:" opt; do
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
        n)
            COUNT="${OPTARG}"
            ;;
        p)
            EXPERIMENT_PARAMS_ARG="-p${OPTARG}"
            ;;
        r)
            CONTROL_SEED="-s${OPTARG}"
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
        ARGS="8 35 3"
        ;;
    medium)
        ARGS="200 870 3"
        ;;
    hard)
        ARGS="500 2000 3"
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
echo "Testing binary ${EXPERIMENT_BINARY} using ${CONTROL_BINARY} as control."

make ${CONTROL_BINARY}
if [[ "$?" != 0 ]]; then exit "$?"; fi
make ${EXPERIMENT_BINARY}
if [[ "$?" != 0 ]]; then exit "$?"; fi

LABEL="label:${DIFFICULTY}"
NSUCCESS=0
NFAILURE=0
NTIMEOUT=0

start=`date +%s`
overall_delta=0

echo "Testing ${DIFFICULTY} examples:"
for i in $(seq 1 "$COUNT"); do
    seed="${RANDOM}"
    printf "rand ${ARGS} ${seed} "
    ./gen/rand.py ${ARGS} ${seed} >| /tmp/test.cnf
    control_start=`date +%s%N`
    control_output="$(timeout ${TIMEOUT} ${CONTROL_BINARY} ${CONTROL_SEED} /tmp/test.cnf 1>/dev/null 2>&1)"
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
    overall_delta=$(bc <<<"scale=1;${overall_delta}+${total_secs}")
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
        printf $'\u001b[32m\u2714\u001b[0m'" (\u0394 = ${total_secs}s)\n" # Green check
        ((NSUCCESS++))
    elif [[ "$control_result" -eq "$UNSATISFIABLE" ]] && [[ "$experiment_result" -eq "$UNSATISFIABLE" ]]; then
        printf $'\u001b[33m\u2714\u001b[0m'" (\u0394 = ${total_secs}s)\n" # Yellow check
        ((NSUCCESS++))
    else
        printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
        ((NFAILURE++))
    fi
done
echo ""

end=`date +%s`
runtime=$((end-start))

echo -e "${NSUCCESS} succeeded, ${NFAILURE} failed, ${NTIMEOUT} timed out in ${runtime} seconds." 'Total \u0394' "= ${overall_delta}s"
