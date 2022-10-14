#!/bin/bash

orig_file=$1
tg_file=$2

if [[ "$orig_file" == "" ]]; then
  echo "Original file not specified"
  exit 1
fi

if [[ "$tg_file" == "" ]]; then
  echo "Target Tamgram file not specified"
  exit 1
fi

if [ ! -f "$orig_file" ]; then
  echo "File does not exist"
  exit 1
fi

if [ ! -f "$tg_file" ]; then
  echo "File does not exist"
  exit 1
fi

rules=$(grep "rule" "$orig_file" | awk '{ print $2 }' | tr -d ':')

for rule in ${rules[@]}; do
  if ! grep -q "$rule" "$tg_file"; then
    echo "$rule is missing"
  fi
done
