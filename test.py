#!/usr/bin/python3

import sys
import os
import re

def check_1():
	res = open(".out", "r")
	lines = res.read().split("\n")
	res.close()

	return lines == ["#", ""]

def check_2_to_3():
	res = open(".out", "r")
	lines = res.read().split("\n")
	res.close()

	return lines == ["", "Impossible!", "", ""]

def check_4_to_51(n):
	res = open(".out", "r")
	lines = res.read().split("\n")
	res.close()

	if (len(lines) != n + 1 or any(not re.match(r"[#.]{" + str(n) + "}", line) for line in lines[:(n - 1)])):
		return False

	for i in range(n):
		for j in range(n):
			if (lines[i][j] == '.'):
				continue

			for k in range(n):
				for l in range(n):
					if (lines[k][l] == '.' or (i == k and j == l)):
						continue

					if (i == k or j == l or abs(i - k) == abs(j - l)):
						return False

	return True

error_count = 0

# --- n = 1 ---

print("Test n = 1:", end = " ")

os.system("./fersat.py 1 > .out")

if (check_1()):
	print("ok")
else:
	print("failed!")
	error_count += 1

# --- n = 2..3 ---

print("Test n = 2:", end = " ")

os.system("./fersat.py 2 > .out")

if (check_2_to_3()):
	print("ok")
else:
	print("failed!")
	error_count += 1

print("Test n = 3:", end = " ")

os.system("./fersat.py 3 > .out")

if (check_2_to_3()):
	print("ok")
else:
	print("failed!")
	error_count += 1

# --- n = 4..50 ---

for n in range(4, 51):
	print(f"Test n = {n}:", end = " ")

	os.system(f"./fersat.py {n} > .out")

	if (check_4_to_51(n)):
		print("ok")
	else:
		print("failed!")
		error_count += 1

os.system("rm .out")
print(f"{error_count} error(s)")
