#!/bin/bash

make

echo "Testing label:satisfiable, label:easy:"
for filename in $(grep -l 'label:easy' test/*.cnf | xargs grep -l 'label:satisfiable'); do
    bin/btwl $filename 1>/dev/null 2>&1
    if [ $? -ne 0 ]; then
        printf 'X'
    else
        printf '.'
    fi
done
echo ""

echo "Testing label:unsatisfiable, label:easy:"
for filename in $(grep -l 'label:easy' test/*.cnf | xargs grep -l 'label:unsatisfiable'); do
    bin/btwl $filename 1>/dev/null 2>&1
    if [ $? -eq 0 ]; then
        printf 'X'
    else
        printf '.'
    fi
done
echo ""
