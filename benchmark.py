import argparse
import glob
import os
from bench_utils import *

parser = argparse.ArgumentParser(description='Benchmark.')
# parser.add_argument('--dir', help='directory to use')
parser.add_argument('--pat', help='pattern')
parser.add_argument('--tgonly', action="store_true")
parser.add_argument('--tmonly', action="store_true")
parser.add_argument('--core', help='core count', default=4)
parser.add_argument('--maxmemory', help='maximum memory', default="50G")
parser.add_argument('--timeout', help='timeout for Tamarin command', default="60m")

args = parser.parse_args()

if args.pat is None:
    pattern = "**.tg"
else:
    pattern = args.pat + ".tg"

config = {}

config["core"] = args.core
config["maxmemory"] = args.maxmemory
config["timeout"] = args.timeout

if args.tgonly and args.tmonly:
    print("--tgonly conflicts with --tmonly")
    exit(1)

if args.tgonly:
    config["exts"] = [ ".tg.spthy" ]
elif args.tmonly:
    config["exts"] = [ ".spthy" ]
else:
    config["exts"] = [ ".spthy", ".tg.spthy" ]

cases = benchmark_cases(pattern)

for case in cases:
    print(case)
