#!/usr/bin/env bash

HERE=$(cd `dirname $0`; pwd)
SPDZROOT=$HERE/..

export PLAYERS=3

. $HERE/run-common-1-core.sh

run_player bgin19-ring-party.x $* || exit 1
