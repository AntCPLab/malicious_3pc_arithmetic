#!/usr/bin/env bash

HERE=$(cd `dirname $0`; pwd)
SPDZROOT=$HERE/..

export PLAYERS=3

. $HERE/run-common-10-core.sh

run_player bgin19-ring-party-multithread.x $* || exit 1
