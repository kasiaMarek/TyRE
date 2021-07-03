#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt

IDRIS2 = "idris2"

iterations = 15

# compile the file to simple
os.system(IDRIS2 + " -p contrib -p tyre Simple.idr -o simple")

times = []
for i in range(iterations):
    ssh = subprocess.Popen(["./build/exec/simple"], stdin=subprocess.PIPE, universal_newlines=True, stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=str(i))[0]
    end = time.time()
    times.append(end - start)
    print(end - start)

plt.plot(range(iterations), times)
plt.savefig('out.png')
