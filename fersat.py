#!/usr/bin/python3

import sys
import os
import subprocess

try:
	# Get script location
	SCRIPT_PATH = sys.path[0]

	# Here must be relative path from this script to Cadical SAT solver
	PATH_TO_SAT_SOLVER = "cadical/cadical"

	args = sys.argv
	if (len(args) <= 1):
		print("N is missing")
		exit(1)

	n = int(args[1])

	# Get variable by cell
	def get_var(i, j):
		return i * n + j + 1

	cnf = []

	# Constraints for one row
	for i in range(n):
		for j in range(n):
			for k in range(j + 1, n):
				cnf.append([-get_var(i, j), -get_var(i, k)])

	# Constraints for one column
	for j in range(n):
		for i in range(n):
			for k in range(i + 1, n):
				cnf.append([-get_var(i, j), -get_var(k, j)])

	# Constraints for northwestern diagonal (like \)
	for i in range(n):
		for j in range(n):
			for k in range(1, min(n - i, n - j)):
				cnf.append([-get_var(i, j), -get_var(i + k, j + k)])

	# Constraints for northeastern diagonal (like /)
	for i in range(n):
		for j in range(n):
			for k in range(1, min(n - i, j + 1)):
				cnf.append([-get_var(i, j), -get_var(i + k, j - k)])

	# Constraints that each row must have at least one queen
	for i in range(n):
		clause = []
		for j in range(n):
			clause.append(get_var(i, j))

		cnf.append(clause)

	# Writing constraints to temp file called ".cnf"
	out = open(".cnf", "w")
	out.write("c CNF formula for N-Queens problem.\n")
	out.write(f"p cnf {n * n} {len(cnf)}\n")
	for clause in cnf:
		for var in clause:
			out.write(f"{var} ")
		
		out.write("0\n")

	out.close()

	# Calling SAT solver and writing the result into temp file called ".result"
	ret_code = subprocess.call(f"{SCRIPT_PATH}/{PATH_TO_SAT_SOLVER} -w .result -q .cnf", shell = True)
	if (ret_code != 10 and ret_code != 20):
		raise RuntimeError("Solver not found or crashed!")

	# Reading data from file ".result"
	res = open(".result", "r")
	lines = list(filter(lambda s: s, res.read().split("\n")))
	res.close()

	# Parsing result of satisfiability check
	def get_sat_result(lines):
		if (not lines):
			raise RuntimeError("Unknown error!")

		if (len(lines[0].split()) != 2 or lines[0].split()[0] != "s"):
			raise RuntimeError("Unknown error!")

		return lines[0].split()[1] == "SATISFIABLE"

	if (not get_sat_result(lines)):
		print("\nImpossible!\n")
		exit(0)

	# Parsing values of variables
	def get_var_values(lines):
		values = [False] * (n * n + 1)
		for line in lines[1:]:
			sp_line = line.split()
			if (sp_line[0] != "v"):
				raise RuntimeError("Unknown error!")

			for lit in sp_line[1:]:
				var = abs(int(lit))
				if (int(lit) > 0):
					values[var] = True

		return values

	# Printing the resulting chess board
	values = get_var_values(lines)
	for i in range(n):
		for j in range(n):
			if (values[get_var(i, j)]):
				print("#", end = "")
			else:
				print(".", end = "")

		print()

except RuntimeError as e:
	print(e)
	print(type(e))

finally:
	os.system("rm .cnf .result")
	out.close()
	res.close()
