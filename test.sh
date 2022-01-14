#!/bin/bash
benchmark_files=$(find . -name "*.smt2")
benchmark_status_regex="(un)?sat"

dub build

for file in $benchmark_files; do
    echo "$file"
    actual=$(./smt-d --file $file | tail -n 1)
    status=$?
    if [ $status -ne 0 ]; then
        echo "An error occured while running smt-d, return code $status"
        exit 2
    fi
    expected=$(cat "$file" | grep -oE "$benchmark_status_regex" | head -n 1)
    if [ "$actual" != "$expected" ]; then
        echo "Expected $expected, but got $actual"
        exit 1
    fi
done

echo "test succeeded"