import os
import glob
import re

tg_file_dir = "examples"

def check_dirs():
    if not (os.path.exists(tg_file_dir) and os.path.isdir(tg_file_dir)):
        print(f"Tamgram file directory {tg_file_dir} not found")
        exit(1)

def tg_files(pattern):
    files = glob.glob(tg_file_dir + "/" + "**/**.tg", recursive=True)
    files.sort()
    return files

def benchmark_cases(pattern="**.tg"):
    files = tg_files(pattern)
    return [x.removesuffix(".tg") for x in files]

def lemmas_of_benchmark_case(name):
    tg_file = name + ".tg"
    lemmas = []
    p_lemma = re.compile("^\s*lemma")
    with open(tg_file) as file:
        lines = file.readlines()
        for line in lines:
            if p_lemma.match(line) is not None:
                lemmas.append(line.split(' ')[1].split('[')[0])

    return lemmas

def check_variant(variant):
    if variant != "tamarin" and variant != "tamgram":
        raise Exception("Invalid file variant: {variant}")

def summary_of_lemma(basedir, name, lemma, variant):
    check_variant(variant)
    if variant == "tamarin":
        suffix = ".spthy.summary"
    elif variant == "tamgram":
        suffix = ".tg.spthy.summary"

    p = re.compile("[A-Za-z0-9-_: ]*\(([a-z-]+)\)[A-Za-z0-9-_: ]*\(([0-9]+) steps\)")

    try:
        summary = {}
        path = f"{basedir}/{name}/{lemma}{suffix}"
        with open(path) as file:
            line = file.read().strip()
        if "verified" in line:
            summary["status"] = "verified"
        elif "falsified" in line:
            summary["status"] = "falsified"
        else:
            raise Exception(f"Failed to classify summary {path}")

        summary["step_count"] = int(p.match(line).group(2))

        return summary
    except:
        return None

def time_of_lemma(basedir, name, lemma, variant):
    check_variant(variant)
    if variant == "tamarin":
        suffix = ".spthy.time"
    elif variant == "tamgram":
        suffix = ".tg.spthy.time"

    try:
        path = f"{basedir}/{name}/{lemma}{suffix}"
        with open(path) as file:
            line = file.read().strip()
        return line
    except:
        return None
