#!/bin/bash

CORE=4
MEMORY=50G
TIMEOUT=60m

if [[ "$1" == "" ]]; then
  pattern='*'
else
  pattern="$1"
fi

tg_files=$(find examples/ -type f -name "$pattern*.tg")

timestamp=$(date +%Y-%m-%d_%H%M)

for file in ${tg_files[@]}; do
  # name=$(basename $file ".tg")
  path_no_ext=${file%.*}

  dir="bench_"$timestamp/$path_no_ext

  mkdir -p $dir

  if [[ "$2" == "tgonly" ]]; then
    exts=(".tg.spthy")
  elif [[ "$2" == "tmonly" ]]; then
    exts=(".spthy")
  else
    exts=(".spthy" ".tg.spthy")
  fi

  for ext in ${exts[@]}; do
    file="$path_no_ext""$ext"

    echo "Benchmarking file:" $file

    if [ ! -f "$file" ]; then
      echo "- File does not exist"
    else
      lemmas=$(grep -E '^[[:space:]]*lemma' $file | awk -F'[[| :]' '{ print $2 }')
      
      for lemma in ${lemmas[@]}; do
        echo "- Benchmarking lemma:" $lemma

        output=$dir/$lemma"$ext".proof

        t0=$(date +%s.%N)

        timeout "$TIMEOUT" \
          tamarin-prover \
          +RTS -N"$CORE" -M"$MEMORY" -RTS \
          --prove=$lemma \
          --output=$output \
          "$file" \
          2>/dev/null \
          | sed -n -e '/summary/,$p' \
          | grep "$lemma" \
          | tail -n 1 \
          | xargs echo \
          >$dir/$lemma"$ext".summary

        t1=$(date +%s.%N)

        duration=$(awk -v a="$t1" -v b="$t0" 'BEGIN { printf "%s", a-b }' </dev/null)

        echo $duration >$dir/$lemma"$ext".time
      done
    fi
  done
done
