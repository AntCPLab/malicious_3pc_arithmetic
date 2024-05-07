import argparse
import re
import subprocess
import os.path
import sys

import datetime

HOST_IP = "172.20.126.23"

PATH = os.getcwd()
PROJECT_PATH = os.path.join(PATH, "..")

parser = argparse.ArgumentParser(description='Run MP-SPDZ benchmark')
parser.add_argument('-i', "--party", type=int, default=0, help='party id')
parser.add_argument('-c', "--cpus", type=int, default=-1, help='number of cpus limit')
parser.add_argument('--nolog', action='store_true', help='log to file')
parser.add_argument('-pn', "--party-number", type=int, default=3, help='number of parties')
parser.add_argument('-pt', "--protocol", type=str, default="aby3", help="MPC protocol uses")
parser.add_argument('-n', "--number", type=int, default=3, help="times to run the benchmark")


args = parser.parse_args()

party_id = args.party

if args.party_number == 3:
    protocol = "./replicated-ring-party.x"
elif args.party_number == 2:
    protocol = "./semi2k-party.x"

if args.protocol == "aby3":
    protocol = "./replicated-ring-party.x"
elif args.protocol == "ours":
    protocol = "./test-ring-party.x"
elif args.protocol == "bgin":
    protocol = "./bgin19-ring-party.x"
elif args.protocol == "sy":
    protocol = "./sy-rep-ring-party.x"
else:
    raise ValueError("Protocol not supported")

if party_id == 0:
    prefix = f"{protocol} 0 -pn 10000 -h 0.0.0.0 "
else:
    prefix = f"{protocol} %d -pn 10000 -h %s --ip-file-name ./mpspdz-ipconfig" % (party_id, HOST_IP)

if args.cpus != -1:
    prefix = ("taskset -c 0-%d " % (args.cpus-1)) + prefix

def run_benchmark(task_name, **kwargs):
    
    # filename example: 
    # 2023-10-12_20-00-00_bubblesort.log
    if not args.nolog:
        filename = protocol + '-' + task_name + '-'
        for key, value in kwargs.items():
            filename += f"{key}-{value}-"

        if filename.endswith("-"):
            filename = filename[:-1]
        filename += ".log"
        f = open(filename, "w")

    command = prefix + task_name + " --verbose"
    for key, value in kwargs.items():
        command += f" -{key} {value}"
    
    time_cost = 0
    communication = 0
    rounds = 0

    for _ in range(args.number):
        print("running", command)
        result = subprocess.run(command, capture_output=True, text=True, shell=True)
        if result.returncode != 0:
            print(result.stdout)
            print(result.stderr)
            exit(1)
        logs = result.stderr
        # print(logs)
        time = float(re.findall(r"Time = (.*?) seconds \n", logs)[0])
        glob_com = float(re.findall(r"Global data sent = (.*?) MB", logs)[0])
        one_round = int(re.findall(r" in ~(.*?) rounds", logs)[0])

        time_cost += time
        communication += glob_com
        rounds += one_round

        if not args.nolog:
            print(logs, file=f)
        
        __import__("time").sleep(1)
    
    time_cost /= args.number
    communication /= args.number
    rounds = int(rounds / args.number)

    print("time = %f\ncomm = %f\nrounds = %d\n\n" % (time_cost, communication, rounds))
    if not args.nolog:
        print("time = %f\ncomm = %f\nrounds = %d\n\n" % (time_cost, communication, rounds), file=f)

if args.protocol == "sy":
    run_benchmark("1M-1", b = 1000000)
    run_benchmark("1M-10", b = 1000000)
    run_benchmark("1M-100", b = 1000000)
    run_benchmark("1M-1000", b = 1000000)

    run_benchmark("10K-10", b = 10000)
    run_benchmark("100K-10", b = 100000)
    run_benchmark("10M-10", b = 10000000)
else:
    run_benchmark("1M-1", b = 10000, ms = 100, tn = 1)
    run_benchmark("1M-10", b = 10000, ms = 100, tn = 1)
    run_benchmark("1M-100", b = 10000, ms = 100, tn = 1)
    run_benchmark("1M-1000", b = 10000, ms = 100, tn = 1)

    run_benchmark("10K-10", b = 10000, ms = 1, tn = 1)
    run_benchmark("100K-10", b = 10000, ms = 10, tn = 1)
    run_benchmark("10M-10", b = 100000, ms = 100, tn = 1)

