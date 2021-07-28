#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt
import statistics

IDRIS2 = "idris2"
SAMPLES = 7
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

def buildTimes(name, iterations):
    timesMatrix = []
    for i in range(SAMPLES):
        timesMatrix.append(measuretime(name, iterations))
    avg = []
    stddev = []
    for i in range(iterations):
        current = []
        for j in range(SAMPLES):
            current.append(timesMatrix[j][i])
        avg.append(statistics.mean(current))
        stddev.append(statistics.stdev(current))
    return {"avg":avg, "stdev":stddev}

def runtest(test):
    itr = test[ITR]
    return {
        "tyretimes": buildTimes(test[TYRE_FILE], itr),
        "combtimes": buildTimes(test[COMB_FILE], itr)
        }

def plotresult(test, testresult):
    tyretimes = testresult["tyretimes"]
    combtimes = testresult["combtimes"]
    y = range(1, test[ITR]+1)
    plt.errorbar(y, tyretimes["avg"], tyretimes["stdev"], marker='^', capsize=3, label='TyRE')
    plt.errorbar(y, combtimes["avg"], combtimes["stdev"], marker='^', capsize=3, label='Parsers Combinators')
    plt.ylabel('time in seconds')
    plt.xlabel(test[XLABEL])
    plt.legend(loc="upper left")
    plt.savefig(PATH_TO_CHARTS + test[NAME] + ".png")
    plt.clf()

tests = [
    {NAME : "alternation", ITR : 17, TYRE_FILE: "AltTyRE", COMB_FILE: "AltComb", XLABEL: "length of regex"},
    {NAME : "concat", ITR : 17, TYRE_FILE: "ConcatTyRE", COMB_FILE: "ConcatComb", XLABEL: "length of regex and word"},
    {NAME : "star", ITR : 17, TYRE_FILE: "StarTyRE", COMB_FILE: "StarComb", XLABEL: "length of word"},
    {NAME : "star2", ITR : 17, TYRE_FILE: "StarTyRE2", COMB_FILE: "StarComb2", XLABEL: "length of word"}
]

def runall():
    results = []
    for t in tests:
        results.append(runtest(t))
    for i in range(len(results)):
        plotresult(tests[i], results[i])

def setIdris(name):
    global IDRIS2
    IDRIS2 = name

def setSamples(n):
    global SAMPLES
    SAMPLES = int(n)

commands = {
    "--idris2" : setIdris,
    "--samples" : setSamples,
}

for a in sys.argv[1:]:
    cm = a.split("=")
    if len(cm) == 2 and cm[0] in commands:
        commands[cm[0]](cm[1])

if not os.path.exists(PATH_TO_CHARTS):
    os.makedirs(PATH_TO_CHARTS)

runall()
