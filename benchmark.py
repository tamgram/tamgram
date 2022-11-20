import argparse
import glob
import os
import pathlib
import subprocess
from datetime import datetime, timedelta
from bench_utils import *

parser = argparse.ArgumentParser(description='Benchmark.')
# parser.add_argument('--dir', help='directory to use')
parser.add_argument('--pattern', help='pattern', default="**")
parser.add_argument('--tgonly', action="store_true")
parser.add_argument('--tmonly', action="store_true")
parser.add_argument('--core', help='core count', default=4)
parser.add_argument('--maxmemory', help='maximum memory', default="50G")
parser.add_argument('--timeout', help='timeout for Tamarin command in minutes', default=60)

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
    pathlib.Path(dir).mkdir(parents=True, exist_ok=True)

    for ext in config["exts"]:
        file = case + ext
        print("Benchmarking file:", file)

        if not os.path.exists(file):
            print("- File does not exist")
        else:
            lemmas = lemmas_of_benchmark_case(case)
            for lemma in lemmas:
                print("- Benchmarking lemma:", lemma)

                proof_file_path = f"{dir}/{lemma}{ext}.proof"
                summary_file_path = f"{dir}/{lemma}{ext}.summary"
                duration_file_path = f"{dir}/{lemma}{ext}.duration"

                t0 = datetime.now()

                args = ["tamarin-prover",
                        "+RTS",
                        f'-N{config["core"]}',
                        f'-M{config["maxmemory"]}',
                        "-RTS",
                        f"--prove={lemma}",
                        f"--output={proof_file_path}",
                        file
                       ]

                timeout = timedelta(minutes=config["timeout"]).total_seconds()

                try:
                    p = subprocess.run(args, timeout=timeout, capture_output=True)
                    summary_section_reached = False
                    for line in p.stdout.splitlines():
                        if "summary" in line.decode("utf-8"):
                            summary_section_reached = True

                        if summary_section_reached:
                            if lemma in line.decode("utf-8"):
                                summary = line.decode("utf-8").strip()
                except subprocess.TimeoutExpired:
                    summary = ""

                t1 = datetime.now()

                with open(summary_file_path, "w") as summary_file:
                    summary_file.write(summary)

                duration = (t1 - t0).total_seconds()

                with open(duration_file_path, "w") as duration_file:
                    duration_file.write(str(duration))
