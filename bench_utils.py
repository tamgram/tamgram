benchmark_dir = "benchmark-latest"

tg_file_dir = "examples"

def check_dirs():
    if not (os.path.exists(tg_file_dir) and os.path.isdir(tg_file_dir)):
        print(f"Tamgram file directory {tg_file_dir} not found")
        exit(1)

def tg_files():
    files = glob.glob(tg_file_dir + "/" + "**/**.tg", recursive=True)
    files.sort()
    return files

def benchmark_cases():
    files = tg_files()
    return [x.removesuffix(".tg") for x in files]

def lemmas_of_benchmark_case(name):
    tg_file = name + ".tg"
    lemmas = []
    with open(tg_file) as file:
        lines = file.readlines()
        for line in lines:
            if p_lemma.match(line) is not None:
                lemmas.append(line.split(' ')[1].split('[')[0])

    return lemmas

def summary_of_lemma_tamarin(name, lemma):
    with open(name + "/" + lemma + ".spthy.summary") as file:
        line = file.read()
    return line

def time_of_lemma_tamarin(name, lemma):
    with open(name + "/" + lemma + ".spthy.time") as file:
        line = file.read()
    return line
