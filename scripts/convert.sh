#!/usr/bin/env bash

# Usage: ./convert_to_csv.sh input.txt output.csv

input="$1"
output="$2"

# Safety check
if [[ -z "$input" || -z "$output" ]]; then
  echo "Usage: $0 input.txt output.csv"
  exit 1
fi

awk '
BEGIN { IFS="\t"; OFS=","; print "benchmark, constraints,HM,gen,solve,total" }
{
  # Remove possible carriage returns
  IFS="\t"
  gsub(/\r/, "")
  if ($1 == "benchmark") n0 = $2
  else if ($1 == "constraints") n1 = $2
  else if ($1 == "HM") n2 = $2
  else if ($1 == "gen") n3 = $2
  else if ($1 == "solve") n4 = $2
  else if ($1 == "real") {
    n5 = $2
    print n0, n1, n2, n3, n4, n5
  }
}
' "$input" > "$output"
