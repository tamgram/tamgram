#!/bin/bash

latest=$(ls -1d bench_* | sort | tail -n 1)

if [[ "$1" == "" ]]; then
  dir_to_use=$latest
else
  dir_to_use="$1"
fi

if [[ "$2" == "" ]]; then
  pattern='*'
else
  pattern="$2"
fi

tg_files=$(find examples/ -type f -name "$pattern*.tg")

for file in ${tg_files[@]}; do
  path_no_ext=${file%.*}

  dir="$dir_to_use"/$path_no_ext
  echo "$dir"

  lemmas=$(grep -E '^[[:space:]]*lemma' $file | awk -F'[[| :]' '{ print $2 }')

  for lemma in ${lemmas[@]}; do
    echo "- Lemma:" $lemma

    echo "  - Tamarin version:"
    echo -n "    - summary: "
    tmp="$dir"/"$lemma".spthy.summary
    if [ ! -f "$tmp" ]; then
      echo "missing"
    else
      cat $tmp
    fi
    echo -n "    - time: "
    tmp="$dir"/"$lemma".spthy.time
    if [ ! -f "$tmp" ]; then
      echo "missing"
    else
      cat $tmp
    fi

    echo "  - Tamgram version:"
    echo -n "    - summary: "
    tmp="$dir"/"$lemma".tg.spthy.summary
    if [ ! -f "$tmp" ]; then
      echo "missing"
    else
      cat $tmp
    fi
    echo -n "    - time: "
    tmp="$dir"/"$lemma".tg.spthy.time
    if [ ! -f "$tmp" ]; then
      echo "missing"
    else
      cat $tmp
    fi
  done
done
