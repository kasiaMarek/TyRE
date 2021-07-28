#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt

IDRIS2 = "idris2"
PATH_TO_CHARTS = "charts/"

NAME = "name"
ITR = "iterations"
TYRE_FILE = "tyreFile"
COMB_FILE = "combFile"
XLABEL = "xlabel"

def measuretime(name, iterations):
    os.system(IDRIS2 + " -p contrib -p tyre " + name + ".idr -o " + name.lower())
    times = []
    for i in range(iterations):
        ssh = subprocess.Popen(["./build/exec/" + name.lower()], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
        start = time.time()
        out = ssh.communicate(input=str(i))[0]
        end = time.time()
        times.append(end - start)
    return times

def runtest(test):
    itr = test[ITR]
    tyretimes = measuretime(test[TYRE_FILE], itr)
    combtimes = measuretime(test[COMB_FILE], itr)
    plt.plot(range(1, itr+1), tyretimes, label='TyRE')
    plt.plot(range(1, itr+1), combtimes, label='Parsers Combinators')
    plt.ylabel('time in seconds')
    plt.xlabel(test[XLABEL])
    plt.legend(loc="upper left")
    plt.savefig(PATH_TO_CHARTS + test[NAME] + ".png")
    plt.clf()

tests = [
    {NAME : "alternation", ITR : 5, TYRE_FILE: "AltTyRE", COMB_FILE: "AltComb", XLABEL: "length of regex"},
    {NAME : "concat", ITR : 5, TYRE_FILE: "ConcatTyRE", COMB_FILE: "ConcatComb", XLABEL: "length of regex and word"},
    {NAME : "star", ITR : 5, TYRE_FILE: "StarTyRE", COMB_FILE: "StarComb", XLABEL: "length of word"},
    {NAME : "star2", ITR : 5, TYRE_FILE: "StarTyRE2", COMB_FILE: "StarComb2", XLABEL: "length of word"}
]

def runall():
    for t in tests:
        runtest(t)

def setIdris(name):
    global IDRIS2
    IDRIS2 = name

commands = {
    "--idris2" : setIdris
}

for a in sys.argv[1:]:
    cm = a.split("=")
    if len(cm) == 2 and cm[0] in commands:
        commands[cm[0]](cm[1])

if not os.path.exists(PATH_TO_CHARTS):
    os.makedirs(PATH_TO_CHARTS)

runall()
