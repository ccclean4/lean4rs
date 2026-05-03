#!/bin/bash
set -x
for f in [0-9]*.lean; do lean "$f"; done