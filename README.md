# CNF Conversion and DPLL Solver

## Overview

This project focuses on implementing a logic solver that includes converting sentences from BNF (Backus-Naur Form) to CNF (Conjunctive Normal Form) and solving them using the DPLL (Davis-Putnam-Logemann-Loveland) algorithm.

## Features

- **BNF to CNF Conversion**: Converts sentences presented in BNF to CNF, making them suitable for processing with SAT solvers.
- **DPLL Algorithm**: Implements the DPLL algorithm for determining the satisfiability of sentences represented in CNF.
- **Verbose Mode**: Offers an optional verbose output mode that details each step taken by the DPLL solver, providing insight into the solving process.

## Requirements

- Python 3.8 or higher

## Installation

No specific installation steps are required other than having a Python interpreter. Clone the repository or download the source code to get started.

## Usage

Run the program from the command line, specifying the mode of operation and the input file containing the sentences in BNF or CNF.

```bash
python solver.py -mode [cnf|dpll|solver] -v input_file.txt
```

- `-mode`: Specifies the operation mode. Use `cnf` for BNF to CNF conversion, `dpll` for solving CNF formulas, and `solver` for a full process that converts BNF to CNF and then solves it.
- `-v`: Optional flag for verbose output from the DPLL solver.
- `input_file.txt`: Path to the input file containing the sentences.

## Input File Format

- For BNF to CNF conversion and full process mode (`solver`), the input file should contain sentences in BNF.
- For DPLL mode, the input file should contain sentences in CNF, where each line represents a separate clause.

# Example Usage

```bash
python solver.py -mode cnf bnf_input.txt
python solver.py -mode dpll cnf_input.txt
python solver.py -mode dpll -v cnf_input.txt
python solver.py -mode solver bnf_input.txt
python solver.py -mode solver -v bnf_input.txt
```

## Output

- For CNF conversion, the output is the CNF representation of the input formula, printed to the console.
- For DPLL solving, the output is either the assignment of variables that satisfies the formula or a message indicating that no solution exists.

## Implementation Details

The project consists of several key components working together to achieve the transformation and solving of logical expressions:

### BNF to CNF Conversion

- **Parsing BNF**: The input BNF formulas are parsed into an abstract syntax tree (AST) representing the logical structure of the expressions.
- **CNF Transformation**: Using the AST, the program applies logical equivalences to transform the formula into CNF. This process involves eliminating implications, moving negations inwards (using De Morgan's laws), and distributing ORs over ANDs to achieve the CNF structure.

### DPLL Solver

- **Clause Extraction**: From the CNF AST, the solver extracts individual clauses (disjunctions of literals) for processing.
- **Satisfiability Solving**: The DPLL algorithm is employed to determine the satisfiability of the CNF formula. It iteratively applies simplifications, including finding and propagating pure literals and unit clauses, and makes guesses for unresolved literals, backtracking as necessary.

## Project Structure

The project is structured around modular components for parsing, conversion, and solving, facilitating clear separation of concerns and extendibility. The core modules include:
- `parser.py`: Parses input formulas into ASTs.
- `cnf_converter.py`: Transforms ASTs from BNF to CNF.
- `dpll_solver.py`: Implements the DPLL algorithm on CNF ASTs or clauses.
- `solver.py`: The main script coordinating the conversion and solving processes based on command-line inputs.
