import argparse
import glob
import os
from datetime import datetime
from bench_utils import *

parser = argparse.ArgumentParser(description='Benchmark.')
# parser.add_argument('--dir', help='directory to use')
parser.add_argument('--pattern', help='pattern', default="**")
parser.add_argument('--tgonly', action="store_true")
parser.add_argument('--tmonly', action="store_true")
parser.add_argument('--core', help='core count', default=4)
parser.add_argument('--maxmemory', help='maximum memory', default="50G")
parser.add_argument('--timeout', help='timeout for Tamarin command', default="60m")

args = parser.parse_args()

config = {}

config["pattern"] = args.pattern
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

cases = benchmark_cases(config["pattern"])

timestamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")

for case in cases:
    dir = f"bench_{timestamp}/{case}"
    print(dir)

    for ext in config["exts"]:
        file = case + ext
        print("Benchmarking file:", file)

        if not os.path.exists(file):
            print("- File does not exist")
        else:
            lemmas = lemmas_of_benchmark_case(case)
            for lemma in lemmas:
                print("- Benchmarking lemma:", lemma)

                output = f"{dir}/{lemma}{ext}.proof"

                t0 = datetime.now()

                t1 = datetime.now()

                duration = (t1 - t0).total_seconds()
