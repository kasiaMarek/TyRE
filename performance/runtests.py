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

NAME = "name"
ITR = "iterations"
TYRE_FILE = "tyreFile"
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

# Execute the program and measure its run time.
def exec(name, i):
    ssh = subprocess.Popen(["./build/exec/" + name],
                            stdin=subprocess.PIPE,
                            universal_newlines=True,
                            stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    return (end - start)

# Measure programs execute times for 0 to ITR.
# Returns a list of results.
def measuretime(name, iterations):
    # compile the program
    os.system(IDRIS2 + " -p tyre -p contrib " + name + ".idr -o " + name.lower())
    times = []
    # warm up run
    exec(name.lower(), 0)
    # exec for n from 0 to ITR
    for i in range(iterations):
        times.append(exec(name.lower(), i))
    return times

# Build times for a program.
# Returns a dictionary with:
#   avg: list of average execution times
#   stdev: list of stdev
def buildTimes(name, iterations):
    timesMatrix = []
    # for number of samples measure program run times
    for i in range(SAMPLES):
        times = measuretime(name, iterations)
        timesMatrix.append(times)
    # build avg and stdev lists
    avg = []
    stddev = []
    for i in range(iterations):
        current = []
        for j in range(SAMPLES):
            current.append(timesMatrix[j][i])
        avg.append(statistics.mean(current))
        stddev.append(statistics.stdev(current))
    return {"avg":avg, "stdev":stddev}

# Build results for both libraries.
def runtest(test):
    result = {
        "tyretimes": buildTimes(test[TYRE_FILE], test[ITR]),
        "combtimes": buildTimes(test[COMB_FILE], test[ITR])
        }
    return result

# A function that plots the results
def plotresult(test, testresult):
    tyretimes = testresult["tyretimes"]
    combtimes = testresult["combtimes"]
    x = range(1, test[ITR]+1)
    #plot average line for tyre
    plt.plot(x, tyretimes["avg"], color='blue', label='TyRE library')
    #plot stddev for tyre
    plt.fill_between(x,
        listOpByIndex(tyretimes["avg"], tyretimes["stdev"], subtract),
        listOpByIndex(tyretimes["avg"], tyretimes["stdev"], add),
        color='blue', alpha=0.2)
    #plot average line for parsers combinators library
    plt.plot(x, combtimes["avg"], color='orange', label='Idris 2\'s stdlib parsers\' combinators library')
    #plot stddev for parsers combinators library
    plt.fill_between(x,
        listOpByIndex(combtimes["avg"], combtimes["stdev"], subtract),
        listOpByIndex(combtimes["avg"], combtimes["stdev"], add),
        color='orange', alpha=0.3)
    #add labes and legend
    plt.ylabel('time in seconds')
    plt.xlabel(test[XLABEL])
    plt.legend(loc="upper left")
    #save the figure
    plt.savefig(PATH_TO_CHARTS + test[NAME] + ".png")
    plt.clf()

# List of all the tests to be runned, each ditectory has the following keys:
# NAME: output file with chart will be ${NAME}.png.
# ITR: we execute the test for n from 0 to ITR
# TYRE_FILE: name of the tyre program to be runned
# COMB_FILE: name of the parser's combinators program to be runned
#   for both we execute the `main` function and pass `n` to it
# XLABEL: Will be printed below the chart.
tests = [
    {NAME : "star", ITR : 1000, TYRE_FILE: "StarTyRE",
        COMB_FILE: "StarComb", XLABEL: "length of word"},
    {NAME : "star2", ITR : 1000, TYRE_FILE: "StarTyRE2",
        COMB_FILE: "StarComb2", XLABEL: "length of word"},
    {NAME : "concat", ITR : 1000, TYRE_FILE: "ConcatTyRE",
        COMB_FILE: "ConcatComb", XLABEL: "length of regex and word"} ,
    {NAME : "alternation", ITR : 1000, TYRE_FILE: "AltTyRE",
        COMB_FILE: "AltComb", XLABEL: "length of regex"}
]

# The main function that is executed.
# We run each test one and plot the results for it.
def runall():
    for t in tests:
        plotresult(t, runtest(t))

def setIdris(name):
    global IDRIS2
    IDRIS2 = name

def setSamples(n):
    global SAMPLES
    SAMPLES = int(n)

# Possibile flags to be passed for execution.
commands = {
    "--idris2" : setIdris,
    "--samples" : setSamples,
}

# Change global params according to the passed flags.
for a in sys.argv[1:]:
    cm = a.split("=")
    if len(cm) == 2 and cm[0] in commands:
        commands[cm[0]](cm[1])

# Create the output directory.
if not os.path.exists(PATH_TO_CHARTS):
    os.makedirs(PATH_TO_CHARTS)

runall()
