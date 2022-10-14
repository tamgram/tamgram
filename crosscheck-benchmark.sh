#!/bin/bash

latest=$(ls -1d bench_* | sort | tail -n 1)

if [[ "$1" == "" ]]; then
  pattern='*'
else
  pattern="$1"
fi

tg_files=$(find examples/ -type f -name "$pattern*.tg")

for file in ${tg_files[@]}; do
  path_no_ext=${file%.*}

  dir="$latest"/$path_no_ext

  lemmas=$(grep -E '^[[:space:]]*lemma' $file | awk -F'[[| :]' '{ print $2 }')

  mismatch_count=0

  for lemma in ${lemmas[@]}; do
    tamarin_ver_summary="$dir"/"$lemma".spthy.summary
    if [ ! -f "$tamarin_ver_summary" ]; then
      continue
    fi
    if [[ $(cat "$tamarin_ver_summary") == *"verified"* ]]; then
      tamarin_ver_res="verified"
    else
      tamarin_ver_res="falsified"
    fi

    tamgram_ver_summary="$dir"/"$lemma".tg.spthy.summary
    if [ ! -f "$tamgram_ver_summary" ]; then
      continue
    fi
    if [[ $(cat "$tamgram_ver_summary") == *"verified"* ]]; then
      tamgram_ver_res="verified"
    else
      tamgram_ver_res="falsified"
    fi

    if [[ "$tamarin_ver_res" != "$tamgram_ver_res" ]]; then
      if (( $mismatch_count == 0 )); then
        echo "Mismatches detected in: $dir"
      fi
      echo "- Lemma:" $lemma
      echo "  - Tamarin version:"
      echo -n "    - "
      cat $tamarin_ver_summary

      echo "  - Tamgram version:"
      echo -n "    - "
      cat $tamgram_ver_summary
      mismatch_count=$(($mismatch_count+1))
    fi
  done

  if (( $mismatch_count == 0 )); then
    echo "No mismatch for: $dir"
  fi
done
