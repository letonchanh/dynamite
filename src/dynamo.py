import os, sys

cwd = os.getcwd()
os.chdir("../deps/dig/src")
dig_path = os.getcwd()
sys.path.append(dig_path)
os.chdir(cwd)

import alg as dig_alg
