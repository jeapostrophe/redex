#!/bin/sh

for p in icfp2005 icfp2009 oopsla2010 ; do
    echo ${p}:
    cd ${p}
    if [ -f all-test.rkt ] ; then
        if ! (rk all-test.rkt) ; then
            exit 1
        fi
    fi
    if [ -f randomized-tests.rkt ] ; then
        for kind in "--unique-decomposition 100" "--CMT-range 100" "--CMT-range-rules 10" "--same-result 50" "--same-result-rules 10" ; do
            echo ${p}: ${kind}:
            if ! (rk randomized-tests.rkt -m -- ${kind}) ; then
                exit 1
            fi
        done
    fi
    cd ..
    echo
done
