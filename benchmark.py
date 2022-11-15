import argparse
import glob
import os
from bench_utils import *

parser = argparse.ArgumentParser(description='Benchmark.')
parser.add_argument('--dir', help='directory to use')
parser.add_argument('--pat', help='pattern')

args = parser.parse_args()

if args.pat is None:
    pattern = "**.tg"
else:
    pattern = args.pat + ".tg"

