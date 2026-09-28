#!/bin/sh
# Steps (a), (b) of certificate.sage at 337 and 1033, and the full run (with the search) at 193.
cd $(dirname "$0")
sage certificate.sage 337 > certificate_p337.out 2>&1
sage certificate.sage 1033 > certificate_p1033.out 2>&1
/usr/bin/time -f "%e s %M KB" sage certificate.sage 193 tree > certificate_p193.out 2>&1
