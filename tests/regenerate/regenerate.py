#!/usr/bin/python

import sys
import os
import subprocess
import time

IDRIS2 = "idris2"
SAMPLES = 5
regexes = ["email", "url", "time", "date", "iso"]

def getStringRegex(name):
    ssh = subprocess.Popen(["./build/exec/gen"],
                            stdin=subprocess.PIPE,
                            universal_newlines=True,
                            stdout=subprocess.PIPE)
    strRegex = ssh.communicate(input=name)[0]
    return strRegex.replace("\\\\", "\\").strip()

def genMatchingStrings(regex):
    process = subprocess.Popen("/bin/bash", shell=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, universal_newlines=True)
    out = process.communicate(input="eval $(opam config env)\nregenerate generate \"{}\" --bound={}".format(regex,SAMPLES))[0]
    return out.splitlines()

def runMatch(regex, string):
    ssh = subprocess.Popen(["./build/exec/parse"],
                            stdin=subprocess.PIPE,
                            universal_newlines=True,
                            stdout=subprocess.PIPE)
    start = time.time()
    result = ssh.communicate(input="{}\n{}".format(regex, string))[0]
    end = time.time()
    return (end - start, result.strip())

def compile():
    os.system(IDRIS2 + " -p tyre -p contrib GenStrings.idr -o gen")
    os.system(IDRIS2 + " -p tyre -p contrib RunRegex.idr -o parse")

def runall():
    compile()
    print("finished compiling")
    for re in regexes:
        print("-------")
        strRe = getStringRegex(re)
        #print("string regex: {}".format(strRe))
        strings = genMatchingStrings(strRe)
        for string in strings:
            (time, result) = runMatch(re, string)
            print("regex: {}, string: {}, result: {}, time: {}".format(re, string, result, time))


def setIdris(name):
    global IDRIS2
    IDRIS2 = name

def setSamples(n):
    global SAMPLES
    SAMPLES = int(n)

def setRegexes(regs):
    global regexes
    regexes = regs.split(",")

commands = {
    "--idris2" : setIdris,
    "--samples" : setSamples,
    "--only" : setRegexes
}

for a in sys.argv[1:]:
    cm = a.split("=")
    if len(cm) == 2 and cm[0] in commands:
        commands[cm[0]](cm[1])

runall()