#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt

IDRIS2 = "idris2"

iterations = 20

# compile idris files
os.system(IDRIS2 + " -p contrib -p tyre StarTyRE.idr -o startyre")
os.system(IDRIS2 + " -p contrib StarCom.idr -o starcomb")

timestyre = []
timescomb = []

for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/startyre"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    timestyre.append(end - start)

for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/starcomb"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    timescomb.append(end - start)

plt.plot(range(iterations), timestyre)
plt.plot(range(iterations), timescomb)
plt.savefig('out.png')
