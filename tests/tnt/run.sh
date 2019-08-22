#!/bin/bash

TEST=$1
TRACE=$2
BND=$3
NUM=$4

javac $TEST.java

> ${TEST}_${TRACE}.tcs
for i in `seq $NUM 1`;
do
    java $TEST > $TEST.out &
    while true; do
        if grep -q 'vtrace2' $TEST.out; then #LOOP EXIT
           break
        elif (( $(grep -c 'vtrace1' $TEST.out) > $BND )); then
            kill $(jps | grep $TEST | awk '{print $1}')
            break
        else
            sleep 0.1
        fi
    done
    grep $TRACE $TEST.out >> ${TEST}_${TRACE}.tcs
done
