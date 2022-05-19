#! /usr/bin/env bash
set -e

NEEDS_SELF_TEST=(scenarios/self_test scenarios/normal_14 scenarios/exceptional_4a
    scenarios/exceptional_4b scenarios/exceptional_4c
    scenarios/exceptional_4d scenarios/exceptional_4e)

for file in ${NEEDS_SELF_TEST[@]}
do
    QUICK=1 RTS_NOCLEAR=1 RTS_DEBUG=1 RTS_BIN=../src/rts.self_test ./test.py $file
done

NO_SELF_TEST=(
    exceptional_2a
    exceptional_3b
    exceptional_5b.cases
    exceptional_5e
    normal_11.cases
    normal_5a.cases
    normal_8.cases
    exceptional_2b
    exceptional_3c
    exceptional_5f
    normal_3a.cases
    normal_6
    exceptional_5c.cases
    normal_12.cases
    normal_1a.cases
    normal_9.cases
    exceptional_2c.cases
    exceptional_5a.cases
    normal_10.cases
    normal_4.cases
    normal_7a.cases
    exceptional_3a
    exceptional_5d.cases
    normal_13.cases
    normal_2a.cases
)

for file in ${NO_SELF_TEST[@]}
do
    QUICK=1 RTS_NOCLEAR=1 RTS_DEBUG=1 RTS_BIN=../src/rts.no_self_test ./test.py $file
done
