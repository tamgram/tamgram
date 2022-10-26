import argparse
from bench_utils import *

check_dirs()

base_dir="benchmark-latest"

def write_summary(file, summary):
    if summary is None:
        file.write("& \\times")
    else:
        file.write("& {0} {1} steps".format(summary["status"], summary["step_count"]))

def write_time(file, time):
    if time is None or time == "":
        file.write("& -")
    else:
        file.write("& {0}".format(time))

def write_table(file, cases, lemmas):
    for case in cases:
        file.write("{0}".format(case.split("/")[-1].replace("_", "\\_")))
        for lemma in lemmas:
            for variant in ["tamarin", "tamgram"]:
                write_summary(file, summary_of_lemma(base_dir, case, lemma, variant))
                write_time(file, time_of_lemma(base_dir, case, lemma, variant))
        file.write("\\\\")
        file.write("\n")

def make_emverify_table0():
    with open(f"{base_dir}/EMVerify_table0.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c *{4}{p{2cm}} *{4}{p{2cm}} },
                    column{4-5,8-9}={blue8},
                }
                &
                \SetCell[c=4]{} executable & & & &
                \SetCell[c=4]{}bank\_accepts & & & \\\\
        """)

        cases = [ x for x in benchmark_cases() if "EMVerify" in x ]

        write_table(file, cases, ["executable", "bank_accepts"])

        file.write("""
            \end{tblr}
        """)

make_emverify_table0()
