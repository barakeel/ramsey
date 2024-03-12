#!/bin/bash

# Set the memory threshold in kilobytes
MEMORY_THRESHOLD_KB=50000000

# Get the current memory usage in kilobytes
AVAILABLE_MEMORY_KB=$(free -k | awk '/Mem/{print $4}')

# Check if memory usage exceeds the threshold
if [ "$AVAILABLE_MEMORY_KB" -lt "$MEMORY_THRESHOLD_KB" ]; then
    # If memory exceeds the threshold, kill the Holmake process
    pkill hol
    echo "hol process killed due to high memory usage: $AVAILABLE_MEMORY_KB KB"
fi
