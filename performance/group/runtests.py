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

ITARATIONS = 12

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

def exec(name, i, isGroup):
    ssh = subprocess.Popen(["./build/exec/" + name],
                            stdin=subprocess.PIPE,
                            universal_newlines=True,
                            stdout=subprocess.PIPE)
    start = time.time()
    group = "no_group"
    if isGroup:
      group = "group"
    out = ssh.communicate(input=group + "\n" + str(i))[0]
    end = time.time()
    return (end - start)

def measuretime(name, iterations, isGroup):
    os.system(IDRIS2 + " -p tyre -p contrib " + name + ".idr -o " + name.lower())
    times = [exec(name.lower(), 0, isGroup)]
    for i in range(iterations):
        times.append(exec(name.lower(), i, isGroup))
    return times

def buildTimes(name, isGroup, iterations):
    timesMatrix = []
    for i in range(SAMPLES):
        times = measuretime(name, iterations, isGroup)
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

def runtest():
  return {
    "balanced": buildTimes("AltBalanced", False, ITARATIONS),
    "unbalanced": buildTimes("AltUnbalanced", False, ITARATIONS),
    "balancedGroup": buildTimes("AltBalanced", True, ITARATIONS),
    "unbalancedGroup": buildTimes("AltUnbalanced", True, ITARATIONS),
  }

def plotresult(testresult):
    balanced = testresult["balanced"]
    unbalanced = testresult["unbalanced"]
    balancedGroup = testresult["balancedGroup"]
    unbalancedGroup = testresult["unbalancedGroup"]
    x = [2 ** y for y in range(ITARATIONS)]
    plt.plot(x, balanced["avg"], color='blue', label='balanced')
    plt.fill_between(x,
        listOpByIndex(balanced["avg"], balanced["stdev"], subtract),
        listOpByIndex(balanced["avg"], balanced["stdev"], add),
        color='blue', alpha=0.2)
    plt.plot(x, unbalanced["avg"], color='orange', label='unbalanced')
    plt.fill_between(x,
        listOpByIndex(unbalanced["avg"], unbalanced["stdev"], subtract),
        listOpByIndex(unbalanced["avg"], unbalanced["stdev"], add),
        color='orange', alpha=0.3)
    plt.plot(x, balancedGroup["avg"], color='green', label='balanced group')
    plt.fill_between(x,
        listOpByIndex(balancedGroup["avg"], balancedGroup["stdev"], subtract),
        listOpByIndex(balancedGroup["avg"], balancedGroup["stdev"], add),
        color='green', alpha=0.2)
    plt.plot(x, unbalancedGroup["avg"], color='red', label='unbalanced group')
    plt.fill_between(x,
        listOpByIndex(unbalancedGroup["avg"], unbalancedGroup["stdev"], subtract),
        listOpByIndex(unbalancedGroup["avg"], unbalancedGroup["stdev"], add),
        color='red', alpha=0.2)
    plt.ylabel('time in seconds')
    plt.xlabel("alt group")
    plt.legend(loc="upper left")
    plt.savefig(PATH_TO_CHARTS + "group.png")
    plt.clf()

def runall():
    plotresult(runtest())

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
