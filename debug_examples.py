import argparse
import glob
import os
import sys
import subprocess
from bench_utils import *

parser = argparse.ArgumentParser(description='Compile examples.')
parser.add_argument('--dir', help='directory to use', default=tg_file_dir)
parser.add_argument('--stop-before-stage', help="stop before stage", default="20")
parser.add_argument('--dev', action="store_true")
parser.add_argument('--pattern', help='pattern', default="**")

args = parser.parse_args()

change_tg_file_dir(args.dir)

config = {}

config["pattern"] = args.pattern
config["stop_before_stage"] = args.stop_before_stage

if args.dev:
    config["command"] = [ "dune", "exec", "src/tamgram.exe", "--", "debug-tg" ]
else:
    config["command"] = [ "tamgram", "debug-tg" ]

cases = benchmark_cases(config["pattern"])

for case in cases:
    tg_file_path = case + ".tg"

    print("Debug printing file", tg_file_path)

    args = config["command"] + [ tg_file_path, "-", f"--stop-before-stage={config['stop_before_stage']}" ]
    p = subprocess.run(args, stdout=sys.stdout)
    if p.returncode != 0:
        print(f"Debug print for {tg_file_path} failed")
        exit(1)
