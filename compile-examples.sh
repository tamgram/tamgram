#!/bin/bash

styles=(
  "cell-by-cell"
  "frame"
  "frame-minimal0"
  "frame-minimal1"
  "persistent0"
  "frame-minimal-reversed-linking0"
)

if [[ "$*" == *"dev"* ]]; then
  make

  if [[ $? != 0 ]]; then
    exit 1
  fi

  cmd="dune exec src/tamgram.exe -- compile"
else
  cmd="tamgram compile"
fi

if [[ "$*" == *"all-styles"* ]]; then
  gen_all_styles="true"
else
  gen_all_styles="false"
fi

tg_files=$(find examples/ -type f -name "*.tg")

for file in ${tg_files[@]}; do
  echo "Cleaning up for file $file"
  rm -f "$file.spthy"
  for style in ${styles[@]}; do
    rm -f "$file.$style.spthy"
  done

  echo "Compiling file $file"
  $cmd "$file" "$file.spthy" -f
  if [[ $? != 0 ]]; then
    echo "Compilation for $file failed"
    exit 1
  fi
  if [[ "$gen_all_styles" == "true" ]]; then
    for style in ${styles[@]}; do
      $cmd "$file" "$file.$style.spthy" -f --style="$style"
    done
  fi
done

