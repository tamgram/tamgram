import argparse
import glob
import os
from bench_utils import *

parser = argparse.ArgumentParser(description='Display benchmark.')
parser.add_argument('--dir', help='directory to use')
parser.add_argument('--pattern', help='pattern', default="**")
parser.add_argument('--allstyles', action="store_true")

args = parser.parse_args()

config = {}

config["pattern"] = args.pattern
if args.allstyles:
    config["additional_styles"] = additional_styles
else:
    config["additional_styles"] = []

def get_latest_dir():
    l = [ x for x in glob.iglob(os.getcwd() + "/" + "benchmark_*") if os.path.isdir(x) ]
    l.sort()
    if len(l) == 0:
        return None
    else:
        return l[-1]

if args.dir is None:
    dir_to_use = get_latest_dir()
    if dir_to_use is None:
        dir_to_use = "benchmark-latest"
else:
    dir_to_use = args.dir

if dir_to_use is None:
    print("Failed to determine directory to use")
    exit(1)

if not os.path.exists(dir_to_use):
    print(f"Directory {dir_to_use} does not exist")
    exit(1)

tg_file_dir="examples"

if not (os.path.exists(tg_file_dir) and os.path.isdir(tg_file_dir)):
    print(f"Tamgram file directory {tg_file_dir} not found")

cases = benchmark_cases(config["pattern"])

for case in cases:
    print(f"{dir_to_use}/{case}")
    for lemma in lemmas_of_benchmark_case(case):
        print(f"- Lemma: {lemma}")

        print("  - Tamarin version:")
        summary = summary_of_lemma(dir_to_use, case, lemma, "tamarin")
        time = time_of_lemma(dir_to_use, case, lemma, "tamarin")
        print(f"    - summary: {summary}")
        print(f"    - time: {time}")

        print("  - Tamgram version:")
        summary = summary_of_lemma(dir_to_use, case, lemma, "tamgram")
        time = time_of_lemma(dir_to_use, case, lemma, "tamgram")
        print(f"    - summary: {summary}")
        print(f"    - time: {time}")

        for style in config["additional_styles"]:
            print(f"  - Tamgram version ({style}):")
            summary = summary_of_lemma(dir_to_use, case, lemma, "tamgram", style=style)
            time = time_of_lemma(dir_to_use, case, lemma, "tamgram", style=style)
            print(f"    - summary: {summary}")
            print(f"    - time: {time}")
