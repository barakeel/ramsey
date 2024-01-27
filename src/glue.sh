#!/bin/bash

# Remember the current directory
original_directory=$(pwd)

# Execute commands in the 'glue' directory
(
  cd glue
  cp ../def/Holmakefile Holmakefile
  export TMPDIR="$PWD/tmp"
  mkdir tmp
  ../../HOL/bin/Holmake -j $1 | tee ../aaa_log_glue
) &

# Store the PID of the last background process (A)
pid_A=$!

# Execute commands for deleting empty temp files in the background
(
  cd /tmp
  watch -n 600 "find . -maxdepth 1 -type f -name 'MLTEMP*' ! -exec lsof {} \; -exec rm {} \;"
) &

# Wait for the 'glue' process (A) to finish
wait $pid_A

# Terminate the background process for deleting empty temp files (B)
pkill -f "find . -maxdepth 1 -type f -name 'MLTEMP*' ! -exec lsof {} \; -exec rm {} \;"

# Remove temporary files
cd /tmp
rm MLTEMP*

# Return to the original directory
cd "$original_directory"
