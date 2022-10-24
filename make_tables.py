import os
import glob
import argparse
import bench_utils

benchmark_dir = "benchmark-latest"

tg_file_dir = "examples"

if not (os.path.exists(tg_file_dir) and os.path.isdir(tg_file_dir)):
    print(f"Tamgram file directory {tg_file_dir} not found")
    exit(1)

tg_files = glob.glob(tg_file_dir + "/" + "**/**.tg", recursive=True)

for tg_file in tg_files:
    base_dir_name = tg_file.removesuffix(".tg")
    print(f"base name {base_dir_name}")

    with open(tg_file) as file:
        lines = file.readlines()
