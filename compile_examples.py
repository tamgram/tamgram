import argparse
import glob
import os
import subprocess
from bench_utils import *

parser = argparse.ArgumentParser(description='Compile examples.')
parser.add_argument('--dir', help='directory to use', default=tg_file_dir)
parser.add_argument('--all-styles', action="store_true")
parser.add_argument('--dev', action="store_true")
parser.add_argument('--pattern', help='pattern', default="**")

args = parser.parse_args()

change_tg_file_dir(args.dir)

config = {}

config["pattern"] = args.pattern
if args.all_styles:
    config["additional_styles"] = additional_styles
else:
    config["additional_styles"] = []

if args.dev:
    config["command"] = [ "dune", "exec", "src/tamgram.exe", "--", "compile" ]
else:
    config["command"] = [ "tamgram", "compile" ]

cases = benchmark_cases(config["pattern"])

for case in cases:
    tg_file_path = case + ".tg"

    print("Cleaning up for file", tg_file_path)
    rm_f(f"{tg_file_path}.spthy")
    for style in config["additional_styles"]:
        rm_f(f"{tg_file_path}.{style}.spthy")

    print("Compiling file", tg_file_path)

    args = config["command"] + [ tg_file_path, f"{tg_file_path}.spthy", "-f" ]
    p = subprocess.run(args)
    if p.returncode != 0:
        print(f"Compilation for {tg_file_path} failed")
        exit(1)

    for style in config["additional_styles"]:
        args = config["command"] + [ tg_file_path, f"{tg_file_path}.{style}.spthy", "-f", f"--style={style}" ]
        subprocess.run(args)
