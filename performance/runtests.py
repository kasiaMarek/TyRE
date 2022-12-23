#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt
import statistics

IDRIS2 = "idris2"
SAMPLES = 5
PATH_TO_CHARTS = "charts/"
RESULTS_FILE = "results.txt"

NAME = "name"
ITR = "iterations"
TYRE_FILE = "tyreFile"
TYRE_FILE2 = "tyreFile2"
COMB_FILE = "combFile"
XLABEL = "xlabel"

def add(x, y):
    return x + y

def subtract(x, y):
    return x - y

def listOpByIndex(l1, l2, f):
    zipped = zip(l1, l2)
    diff = []
    for e1, e2 in zipped:
        diff.append(f(e1, e2))
    return diff

def exec(name, i):
    ssh = subprocess.Popen(["./build/exec/" + name],
                            stdin=subprocess.PIPE,
                            universal_newlines=True,
                            stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    return (end - start)

def measuretime(name, iterations):
    os.system(IDRIS2 + " -p tyre -p contrib " + name + ".idr -o " + name.lower())
    times = []
    exec(name.lower(), 0)
    for i in range(iterations):
        times.append(exec(name.lower(), i))
    return times

def buildTimes(name, iterations):
    timesMatrix = []
    for i in range(SAMPLES):
        times = measuretime(name, iterations)
        with open(RESULTS_FILE, 'a') as f:
            f.write(name + "-" + str(i) + " : " + str(times) + "\n")
        timesMatrix.append(times)
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
    result = {
        "tyretimes": buildTimes(test[TYRE_FILE], test[ITR]),
        "tyretimes2": buildTimes(test[TYRE_FILE2], test[ITR]),
        "combtimes": buildTimes(test[COMB_FILE], test[ITR]),
        }
    return result

def plotresult(test, testresult):
    tyretimes = testresult["tyretimes"]
    tyretimes2 = testresult["tyretimes2"]
    combtimes = testresult["combtimes"]
    x = range(1, test[ITR]+1)
    plt.plot(x, tyretimes["avg"], color='blue', label='TyRE library')
    plt.fill_between(x,
        listOpByIndex(tyretimes["avg"], tyretimes["stdev"], subtract),
        listOpByIndex(tyretimes["avg"], tyretimes["stdev"], add),
        color='blue', alpha=0.2)
    plt.plot(x, tyretimes2["avg"], color='purple', label='TyRE library typed parser')
    plt.fill_between(x,
        listOpByIndex(tyretimes2["avg"], tyretimes2["stdev"], subtract),
        listOpByIndex(tyretimes2["avg"], tyretimes2["stdev"], add),
        color='purple', alpha=0.2)
    plt.plot(x, combtimes["avg"], color='orange', label='Idris 2\'s stdlib parsers\' combinators library')
    plt.fill_between(x,
        listOpByIndex(combtimes["avg"], combtimes["stdev"], subtract),
        listOpByIndex(combtimes["avg"], combtimes["stdev"], add),
        color='orange', alpha=0.3)
    plt.ylabel('time in seconds')
    plt.xlabel(test[XLABEL])
    plt.legend(loc="upper left")
    plt.savefig(PATH_TO_CHARTS + test[NAME] + ".png")
    plt.clf()

tests = [
    {NAME : "star", ITR : 1000,
        TYRE_FILE: "StarTyRE11", TYRE_FILE2: "StarTyRE12", COMB_FILE: "StarComb",
        XLABEL: "length of word"},
    {NAME : "star2", ITR : 1000,
        TYRE_FILE: "StarTyRE21", TYRE_FILE2: "StarTyRE22", COMB_FILE: "StarComb2",
        XLABEL: "length of word"},
    {NAME : "concat", ITR : 1000,
        TYRE_FILE: "ConcatTyRE", TYRE_FILE2: "ConcatTyRE2", COMB_FILE: "ConcatComb",
        XLABEL: "length of regex and word"} ,
    {NAME : "alternation", ITR : 1000,
        TYRE_FILE: "AltTyRE", TYRE_FILE2: "AltTyRE2", COMB_FILE: "AltComb",
        XLABEL: "length of regex"}
]

def runall():
    for t in tests:
        plotresult(t, runtest(t))

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
