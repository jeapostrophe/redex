#!/bin/bash

run() {
    echo $* && \
	time mred-text -t $*
}

mzc -k *ss

run atotcaia-tests.ss

for i in atotcaia-prop-*ss ; do
    run $i
done