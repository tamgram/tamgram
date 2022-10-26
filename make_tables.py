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
        file.write("& {:.1f}".format(time))

def write_table(file, cases, lemmas):
    for case in cases:
        file.write("{0}".format(case.split("/")[-1].replace("_", "\\_")))
        for lemma in lemmas:
            for variant in ["tamarin", "tamgram"]:
                write_summary(file, summary_of_lemma(base_dir, case, lemma, variant))
                write_time(file, time_of_lemma(base_dir, case, lemma, variant))
        file.write("\\\\")
        file.write("\n")

def make_emverify_table(index, lemmas):
    with open(f"{base_dir}/EMVerify_table{index}.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c 
        """)
        
        for _ in lemmas:
            file.write("*{1}{p{2cm}} *{1}{p{1.5cm}}")
            file.write("*{1}{p{2cm}} *{1}{p{1.5cm}}")

        file.write("""
                    },
                    column{4-5,8-9}={blue8},
                }
        """)

        for lemma in lemmas:
            file.write("& \\SetCell[c=4]{{}} {} & & &".format(lemma.replace("_", "\\_")))

        file.write("\\\\")
        file.write("\n")

        cases = [ x for x in benchmark_cases() if "EMVerify" in x ]

        write_table(file, cases, lemmas)

        file.write("\end{tblr}")

make_emverify_table(0, ["executable", "bank_accepts"])
make_emverify_table(1, ["auth_to_terminal_minimal", "auth_to_terminal"])
make_emverify_table(2, ["auth_to_bank_minimal", "auth_to_bank"])
make_emverify_table(3, ["secrecy_MK", "secrecy_privkCard"])
make_emverify_table(4, ["secrecy_PIN", "secrecy_PAN"])
