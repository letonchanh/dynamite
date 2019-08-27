#!/bin/bash

TEST=$1
TRACE=$2
BND=$3
NUM=$4
VARS=$5

TRACE_TCS=${TEST}_${TRACE}.tcs
TRACE0_TERM_BASE_TCS=${TEST}_vtrace0_term_base.tcs
TRACE0_TERM_REC_TCS=${TEST}_vtrace0_term_rec.tcs
TRACE0_MAYLOOP_TCS=${TEST}_vtrace0_mayloop.tcs
TRACE1_MAYLOOP_TCS=${TEST}_vtrace1_mayloop.tcs
TRACE2_TERM_BASE_TCS=${TEST}_vtrace2_term_base.tcs
TRACE2_TERM_REC_TCS=${TEST}_vtrace2_term_rec.tcs

javac $TEST.java

echo "$TRACE: $VARS" > ${TRACE_TCS}
echo "vtrace0: $VARS" > ${TRACE0_MAYLOOP_TCS}
echo "vtrace0: $VARS" > ${TRACE0_TERM_BASE_TCS}
echo "vtrace0: $VARS" > ${TRACE0_TERM_REC_TCS}
echo "vtrace1: $VARS" > ${TRACE1_MAYLOOP_TCS}
echo "vtrace2: $VARS" > ${TRACE2_TERM_BASE_TCS}
echo "vtrace2: $VARS" > ${TRACE2_TERM_REC_TCS}

for i in `seq $NUM 1`;
do
    java $TEST $BND > $TEST.out
    # while true; do
    #     if grep -q 'vtrace2' $TEST.out; then #LOOP EXIT
    #        break
    #     elif (( $(grep -c 'vtrace1' $TEST.out) > $BND )); then
    #         kill $(jps | grep $TEST | awk '{print $1}')
    #         break
    #     else
    #         sleep 0.1
    #     fi
    # done
    grep $TRACE $TEST.out >> ${TRACE_TCS}

    if grep -q 'vtrace2' $TEST.out; then
        if grep -q 'vtrace1' $TEST.out; then
            grep "vtrace2" $TEST.out >> ${TRACE2_TERM_REC_TCS}
            grep "vtrace0" $TEST.out >> ${TRACE0_TERM_REC_TCS}
        else # BASE CASE
            grep "vtrace2" $TEST.out >> ${TRACE2_TERM_BASE_TCS}
            grep "vtrace0" $TEST.out >> ${TRACE0_TERM_BASE_TCS}
        fi
    else # LOOP REACHES THE BND
        grep "vtrace1" $TEST.out >> ${TRACE1_MAYLOOP_TCS}
        grep "vtrace0" $TEST.out >> ${TRACE0_MAYLOOP_TCS}
    fi
done
