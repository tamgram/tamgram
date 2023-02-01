import argparse
from bench_utils import *

check_dirs()

base_dir="benchmark-latest"

def write_summary(file, summary):
    if summary is None:
        file.write("& $\\times$")
    else:
        file.write("& {0} {1} steps".format(summary["status"], summary["step_count"]))

def write_time(file, summary, time):
    if summary is None and time is not None:
        file.write("& \\texttt{TIMEOUT}")
    elif time is None or time == "":
        file.write("& -")
    else:
        file.write("& {:.1f}".format(time))

def write_table(file, cases, lemmas):
    for case in cases:
        file.write("{0}".format(case.split("/")[-1].replace("_", "\\_")))
        for lemma in lemmas:
            for variant in ["tamarin", "tamgram"]:
                summary = summary_of_lemma(base_dir, case, lemma, variant)
                write_summary(file, summary)
                write_time(file, summary, time_of_lemma(base_dir, case, lemma, variant))
        file.write("\\\\")
        file.write("\n")

def make_csf18_xor_table(case):
    with open(f"{base_dir}/CSF18_XOR_{case}_table.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c 
        """)

        for _ in versions:
            file.write("*{1}{p{1.5cm}} *{1}{p{1cm}}")

        file.write("""
                    },
                    column{4-5,8-9}={blue8},
                }
        """)

def make_csf18_xor_styles_table(name):
    case = f"examples/csf18-xor/{name}"
    lemmas = lemmas_of_benchmark_case(case)
    with open(f"{base_dir}/CSF18_XOR_{name}_table.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c 
        """)

        versions = [("Original", ".spthy"),
                    ("Cell by cell", ".tg.cell-by-cell.spthy"),
                    ("Forward", ".tg.frame-minimal0.spthy"),
                    ("Backward", ".tg.frame-minimal-backward0.spthy"),
                    ("Hybrid", ".tg.spthy"),
                   ]

        for _ in versions:
            file.write("*{1}{p{0.75cm}}")

        file.write("""
                    },
                }
        """)

        for (version, _) in versions:
            file.write("& {}".format(version))

        file.write("\\\\")
        file.write("\n")

        for lemma in lemmas:
            file.write("{}".format(lemma.replace("_", "\\_")))
            for (version, ext) in versions:
                write_time(file,
                           summary_of_lemma(base_dir, case, lemma, ext=ext),
                           time_of_lemma(base_dir, case, lemma, ext=ext))
            file.write("\\\\")
            file.write("\n")

        file.write("\end{tblr}")

def make_csf18_xor_styles_summarized_table(names):
    with open(f"{base_dir}/CSF18_XOR_summarized_table.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c 
        """)
        versions = [("Original", ".spthy"),
                    ("Cell by cell", ".tg.cell-by-cell.spthy"),
                    ("Forward", ".tg.frame-minimal0.spthy"),
                    ("Backward", ".tg.frame-minimal-backward0.spthy"),
                    ("Hybrid", ".tg.spthy"),
                   ]
        for _ in versions:
            file.write("*{1}{p{0.75cm}}")

        file.write("""
                    },
                }
        """)

        for (version, _) in versions:
            file.write("& {}".format(version))

        file.write("\\\\")
        file.write("\n")

        for name in names:
            case = f"examples/csf18-xor/{name}"
            lemmas = lemmas_of_benchmark_case(case)
            for (version, ext) in versions:
                total_time = 0
                for lemma in lemmas:
                    total_time += time_of_lemma(base_dir, case, lemma, ext=ext)
                file.write("& {:.1f}".format(total_time))

            file.write("\\\\")
            file.write("\n")

        file.write("\end{tblr}")

def make_emverify_styles_table(name):
    case = f"examples/EMVerify/contactless/{name}"
    lemmas = lemmas_of_benchmark_case(case)
    with open(f"{base_dir}/EMVerify_contactless_{name}_table.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c 
        """)

        versions = [("Original", ".spthy"),
                    ("Cell by cell", ".tg.cell-by-cell.spthy"),
                    ("Forward", ".tg.frame-minimal0.spthy"),
                    ("Backward", ".tg.frame-minimal-backward0.spthy"),
                    ("Hybrid", ".tg.spthy"),
                   ]

        for _ in versions:
            file.write("*{1}{p{0.75cm}}")

        file.write("""
                    },
                }
        """)

        for (version, _) in versions:
            file.write("& {}".format(version))

        file.write("\\\\")
        file.write("\n")

        for lemma in lemmas:
            file.write("{}".format(lemma.replace("_", "\\_")))
            for (version, ext) in versions:
                write_time(file,
                           summary_of_lemma(base_dir, case, lemma, ext=ext),
                           time_of_lemma(base_dir, case, lemma, ext=ext))
            file.write("\\\\")
            file.write("\n")

        file.write("\end{tblr}")

def make_emverify_table(index, lemmas):
    with open(f"{base_dir}/EMVerify_table{index}.tex", "w") as file:
        file.write("""
            \\begin{tblr}{
                    hlines,
                    vlines,
                    colspec={c 
        """)
        
        for _ in lemmas:
            #file.write("*{1}{p{2cm}} *{1}{p{1.5cm}}")
            #file.write("*{1}{p{2cm}} *{1}{p{1.5cm}}")
            file.write("*{1}{p{1.5cm}} *{1}{p{1cm}}")
            file.write("*{1}{p{1.5cm}} *{1}{p{1cm}}")

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

csf18_xor_cases = ["CH07",
                   "CRxor",
                   "KCL07",
                   "LAK06",
                   "NSLPK3xor",
        ]

for case in csf18_xor_cases:
    make_csf18_xor_styles_table(case)

make_csf18_xor_styles_summarized_table(csf18_xor_cases)

make_emverify_styles_table("Mastercard_CDA_NoPIN_Low")

make_emverify_table(0, ["executable", "bank_accepts"])
make_emverify_table(1, ["auth_to_terminal_minimal", "auth_to_terminal"])
make_emverify_table(2, ["auth_to_bank_minimal", "auth_to_bank"])
make_emverify_table(3, ["secrecy_MK", "secrecy_privkCard"])
make_emverify_table(4, ["secrecy_PIN", "secrecy_PAN"])
