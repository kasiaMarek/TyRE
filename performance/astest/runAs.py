#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt

IDRIS2 = "idris2"

iterations = 15

# compile the file to simple
os.system(IDRIS2 + " -p contrib -p tyre AsTyRE.idr -o asTyre")
os.system(IDRIS2 + " -p contrib AsComb.idr -o asComb")

timesTyre = []
timesComb = []

for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/asTyre"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    timesTyre.append(end - start)
    # print(end - start)

for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/asComb"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    timesComb.append(end - start)
    # print(end - start)

plt.plot(range(iterations), timesTyre)
plt.plot(range(iterations), timesComb)
plt.savefig('out.png')
