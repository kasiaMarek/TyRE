#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt

IDRIS2 = "idris2"

iterations = 8

# compile the file to simple
os.system(IDRIS2 + " -p contrib -p tyre AsTyREMaybe.idr -o asTyreMaybe")

timesExandRE = []
timesConstRE = []

for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/asTyreMaybe"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(iterations) + "\n" + str(i))[0]
    end = time.time()
    timesExandRE.append(end - start)
    print(out)
    print(end - start)
    # print(end - start)

for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/asTyreMaybe"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i) + "\n" + str(i))[0]
    end = time.time()
    timesConstRE.append(end - start)
    print(out)
    print(end - start)

plt.plot(range(iterations), timesExandRE)
plt.plot(range(iterations), timesConstRE)
plt.savefig('outMaybe.png')
