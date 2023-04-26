#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt
import statistics

VERBOSE = True
IDRIS2 = "idris2"
SAMPLES = 5
PATH_TO_CHARTS = "charts/"
ITERATIONS = 1000
YLIM = 0.2

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
    # warm up run
    exec(name.lower(), 0)
    times = []
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

def runtest():
    result = {}
    for (i,j) in [("AltBalanced", "balanced"),
                  ("AltUnbalanced","unbalanced"),
                  ("AltBalancedGroup", "balancedGroup"),
                  ("AltUnbalancedGroup", "unbalancedGroup"),
                  ("AltComb", "combinators")
                 ]:
        if VERBOSE:
            print(f"Running test {j}... ", end='')
            sys.stdout.flush()
        result[j] = buildTimes(i, ITERATIONS)
        if VERBOSE:
            print("done.")
    return result

# Find maximum average and standard deviation of a result
def maxval(testresult):
    vals = [x + y
              for (x,y) in
                zip(testresult["avg"],testresult["stdev"])]
    return max(vals)

# A function that plots the results
def plotresult(testresult):
    balanced = testresult["balanced"]
    unbalanced = testresult["unbalanced"]
    balancedGroup = testresult["balancedGroup"]
    unbalancedGroup = testresult["unbalancedGroup"]
    combinators = testresult["combinators"]
    x = range(ITERATIONS)
    # plot the chart
    plt.plot(x, combinators["avg"], color='orange',
                label='parser combinators')
    plt.fill_between(x,
        listOpByIndex(combinators["avg"], combinators["stdev"], subtract),
        listOpByIndex(combinators["avg"], combinators["stdev"], add),
        color='orange', alpha=0.2)
    plt.plot(x, unbalanced["avg"], color='blue', label='TyRE unbalanced')
    plt.fill_between(x,
        listOpByIndex(unbalanced["avg"], unbalanced["stdev"], subtract),
        listOpByIndex(unbalanced["avg"], unbalanced["stdev"], add),
        color='blue', alpha=0.3)
    plt.plot(x, balanced["avg"], color='magenta', label='TyRE balanced')
    plt.fill_between(x,
        listOpByIndex(balanced["avg"], balanced["stdev"], subtract),
        listOpByIndex(balanced["avg"], balanced["stdev"], add),
        color='magenta', alpha=0.2)
    plt.plot(x, unbalancedGroup["avg"], color='red', label='TyRE unbalanced group')
    plt.fill_between(x,
        listOpByIndex(unbalancedGroup["avg"], unbalancedGroup["stdev"], subtract),
        listOpByIndex(unbalancedGroup["avg"], unbalancedGroup["stdev"], add),
        color='red', alpha=0.2)
    plt.plot(x, balancedGroup["avg"], color='green', label='TyRE balanced group')
    plt.fill_between(x,
        listOpByIndex(balancedGroup["avg"], balancedGroup["stdev"], subtract),
        listOpByIndex(balancedGroup["avg"], balancedGroup["stdev"], add),
        color='green', alpha=0.2)
    #add labes and legend
    plt.ylabel('time in seconds')
    plt.xlabel("alt group")
    plt.legend(loc="upper left")
    #GetCurrentAxes
    ax = plt.gca()
    ax.set_ylim([0.0, YLIM])
    maxy = max([maxval(result)
                  for result in [combinators,unbalanced, balanced, unbalancedGroup, balancedGroup]])
    if VERBOSE and maxy > YLIM:
        print(f"Out-of-frame points for test {test[NAME]}")
    #save the figure
    plt.savefig(PATH_TO_CHARTS + "group.png")
    plt.clf()

def runall():
    plotresult(runtest())

def setIdris(name):
    global IDRIS2
    IDRIS2 = name

# The main function that is executed.
# We run each test one and plot the results for it.
def setSamples(n):
    global SAMPLES
    SAMPLES = int(n)

def setVerbose(b):
    global VERBOSE
    VERBOSE = not ("False" == b)

# Possibile flags to be passed for execution.
commands = {
    "--idris2" : setIdris,
    "--samples" : setSamples,
    "--verbose" : setVerbose,
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
