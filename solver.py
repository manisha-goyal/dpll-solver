import argparse
import sys
import re

class Node:
    pass

class BinaryOperator(Node):
    def __init__(self, left, right):
        self.left = left
        self.right = right

class UnaryOperator(Node):
    def __init__(self, expr):
        self.expr = expr

class Implies(BinaryOperator):
    def __repr__(self):
        return f"({self.left} => {self.right})"

class Iff(BinaryOperator):
    def __repr__(self):
        return f"({self.left} <=> {self.right})"

class And(BinaryOperator):
    def __repr__(self):
        return f"({self.left} & {self.right})"

class Or(BinaryOperator):
    def __repr__(self):
        return f"({self.left} | {self.right})"

class Not(UnaryOperator):
    def __repr__(self):
        return f"!{self.expr}"

class Atom(Node):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

class Parser:
    def __init__(self, tokens):
        self.tokens = iter(tokens)
        self.advance()
    
    def advance(self):
        try:
            self.current_token = next(self.tokens)
        except StopIteration:
            self.current_token = ''
    
    def eat(self, token_value):
        if self.current_token == token_value:
            self.advance()
        else:
            raise Exception(f"Expected token '{token_value}', but found '{self.current_token}', mismatched parentheses or input not in BNF")

    def parse(self):
        if self.current_token == '':
            return None
        result = self.expression()
        if self.current_token != '':
            raise Exception("Unexpected end of input, mismatched parentheses or input not in BNF")
        return result

    def expression(self):
        return self.equivalence()

    def equivalence(self):
        node = self.implication()
        while self.current_token == '<=>':
            self.advance()
            node = Iff(node, self.implication())
        return node

    def implication(self):
        node = self.or_expression()
        while self.current_token == '=>':
            self.advance()
            node = Implies(node, self.or_expression())
        return node

    def or_expression(self):
        node = self.and_expression()
        while self.current_token == '|':
            self.advance()
            right = self.and_expression()
            node = Or(node, right)
        return node

    def and_expression(self):
        node = self.not_expression()
        while self.current_token == '&':
            self.advance()
            right = self.not_expression()
            node = And(node, right)
        return node

    def not_expression(self):
        if self.current_token == '!':
            self.advance()
            node = Not(self.atom())
        else:
            node = self.atom()
        return node

    def atom(self):
        if self.current_token == '(':
            self.advance()
            node = self.expression()
            self.eat(')')
            return node
        elif self.current_token == '{':
            self.advance()
            node = self.expression()
            self.eat('}')
            return node
        elif self.current_token == '[':
            self.advance()
            node = self.expression()
            self.eat(']')
            return node
        else:
            atom_name = self.current_token
            self.advance()
            return Atom(atom_name)

class CNFConverter:
    def __init__(self, root):
        self.root = root

    def remove_iff(self, node):
        if isinstance(node, Iff):
            node.left = self.remove_iff(node.left)
            node.right = self.remove_iff(node.right)
            return And(Implies(node.left, node.right), Implies(node.right, node.left))
        elif isinstance(node, (And, Or)):
            node.left = self.remove_iff(node.left)
            node.right = self.remove_iff(node.right)
        elif isinstance(node, Not):
            node.expr = self.remove_iff(node.expr)
        elif isinstance(node, Atom):
            return node
        return node

    def remove_implies(self, node):
        if isinstance(node, Implies):
            return Or(Not(self.remove_implies(node.left)), self.remove_implies(node.right))
        elif isinstance(node, (And, Or)):
            node.left = self.remove_implies(node.left)
            node.right = self.remove_implies(node.right)
        elif isinstance(node, Not):
            node.expr = self.remove_implies(node.expr)
        elif isinstance(node, Atom):
            return node
        return node

    def to_negation_normal_form(self, node):
        if isinstance(node, Not):
            if isinstance(node.expr, Or):
                return And(self.to_negation_normal_form(Not(node.expr.left)), self.to_negation_normal_form(Not(node.expr.right)))
            elif isinstance(node.expr, And):
                return Or(self.to_negation_normal_form(Not(node.expr.left)), self.to_negation_normal_form(Not(node.expr.right)))
            elif isinstance(node.expr, Not):
                return self.to_negation_normal_form(node.expr.expr)
        elif isinstance(node, (And, Or)):
            node.left = self.to_negation_normal_form(node.left)
            node.right = self.to_negation_normal_form(node.right)
        return node

    def distribution(self, node):
        if isinstance(node, Or):
            if isinstance(node.left, And):
                new_node = And(Or(node.left.left, node.right), Or(node.left.right, node.right))
                return self.distribution(new_node)
            elif isinstance(node.right, And):
                new_node = And(Or(node.right.left, node.left), Or(node.right.right, node.left))
                return self.distribution(new_node)
            else:
                node.left = self.distribution(node.left)
                node.right = self.distribution(node.right)
        elif isinstance(node, And):
            node.left = self.distribution(node.left)
            node.right = self.distribution(node.right)
        elif isinstance(node, Not):
            node.expr = self.distribution(node.expr)
        return node

    def is_cnf(self, node):
        if isinstance(node, Atom) or (isinstance(node, Not) and isinstance(node.expr, Atom)):
            return True
        elif isinstance(node, Not):
            return False
        elif isinstance(node, Or):
            for child in [node.left, node.right]:
                if isinstance(child, And):
                    return False
                if not self.is_cnf(child):
                    return False
        elif isinstance(node, And):
            return self.is_cnf(node.left) and self.is_cnf(node.right)
        return True

    def bnf_to_cnf(self):
        self.root = self.remove_iff(self.root)
        self.root = self.remove_implies(self.root)
        self.root = self.to_negation_normal_form(self.root)
        while not self.is_cnf(self.root):
            self.root = self.distribution(self.root)
        return self.root

    def get_clauses(self, node):
        clauses = []

        def traverse(node):
            if isinstance(node, Atom) or (isinstance(node, Not) and isinstance(node.expr, Atom)):
                return [[str(node)]]
            elif isinstance(node, Not):
                return [[str(node)] + traverse(node.expr)]
            elif isinstance(node, Or):
                combined_clauses = []
                left_clauses = traverse(node.left)
                right_clauses = traverse(node.right)
                for l_clause in left_clauses:
                    for r_clause in right_clauses:
                        combined_clauses.append(l_clause + r_clause)
                return combined_clauses
            elif isinstance(node, And):
                clauses.extend(traverse(node.left))
                clauses.extend(traverse(node.right))
                return []

        traverse(node)
        return [set(clause) for clause in clauses if clause]
   
class DPLLSolver:
    def __init__(self, verbose):
        self.negation = '!'
        self.verbose = verbose

    def find_easy_case(self, clauses):
        curr_literals = {literal for clause in clauses for literal in clause}
        for literal in sorted(curr_literals):
            symbol = literal.strip(self.negation)
            if literal.startswith(self.negation):
                if literal[1:] not in curr_literals:
                    self.print_verbose(f"\nEasy case: {symbol} = False")
                    return literal
            else:
                if self.negation + literal not in curr_literals:
                    self.print_verbose(f"\nEasy case: {symbol} = True")
                    return literal
        for clause in clauses:
            if len(clause) == 1:
                literal = next(iter(clause))
                symbol = literal.strip(self.negation)
                value = False if literal.startswith(self.negation) else True
                self.print_verbose(f"\nEasy case: {symbol} = {value}")
                return literal
        return None

    def simplify_sentences(self, clauses, remove_literal):
        updated_clauses = []
        for clause in clauses:
            if remove_literal in clause:
                continue
            if remove_literal.startswith(self.negation):
                new_clause = clause - {remove_literal.strip(self.negation)}
            else:
                new_clause = clause - {self.negation + remove_literal}
            updated_clauses.append(new_clause)
        if self.verbose:
            for clause in updated_clauses:
                if len(clause) > 0:
                    print(" ".join(clause))
        return updated_clauses
    
    def recursive_dpll(self, all_symbols, clauses, solution):
        easy_case = self.find_easy_case(clauses)
        while easy_case:
            symbol = easy_case.strip(self.negation)
            is_negated = easy_case.startswith(self.negation)
            solution[symbol] = not is_negated
            clauses = self.simplify_sentences(clauses, easy_case)
            for clause in clauses:
                if len(clause) == 0:
                    self.print_verbose(f"\nContradiction: {symbol}")
                    return False, {}
            easy_case = self.find_easy_case(clauses)

        if not clauses:
            if not any(clause for clause in clauses if clause):
                self.print_verbose("")
                for symbol in all_symbols:
                    if symbol not in solution:
                        self.print_verbose(f"Unbounded: {symbol} = False")
                        solution[symbol] = False
                return True, solution
            return False, {}

        for symbol in all_symbols:
            if symbol not in solution:
                for value in [True, False]:
                    self.print_verbose(f"\nHard case, guess: {symbol} = {value}")
                    new_solution = solution.copy()
                    new_solution[symbol] = value
                    new_clauses = self.simplify_sentences(clauses, symbol if value else self.negation + symbol)
                    success, result = self.recursive_dpll(all_symbols, new_clauses, new_solution)
                    if success:
                        return True, result
                    else:
                        self.print_verbose(f"Fail hard case: {symbol} = {value}, backtracking ")
                break
        return False, {}
    
    def solve_dpll(self, clauses, solution={}):
        all_symbols = sorted({literal.strip(self.negation) for clause in clauses for literal in clause})
        return self.recursive_dpll(all_symbols, clauses, solution)
    
    def print_verbose(self, message):
        if verbose:
            print(message)

class InputProcessor:

    def get_input_from_file(self, file_name):
        tokens = []
        with open(file_name) as in_file:
            for line in in_file.readlines():
                if line == '\n':
                    continue
                l = line
                tokens.append(f"({l.strip()})")
        return " & ".join(tokens)

    def tokenize_cnf(self, expression):
        operator_re = re.compile(r"(<=>|=>|!|&|\||\(|\)|\[|\]|\{|\})")
        identifier_re = re.compile(r"[a-zA-Z_][a-zA-Z0-9_]*")
        tokens = []
        i = 0
        while i < len(expression):
            char = expression[i]
            op_match = operator_re.match(expression[i:])
            if op_match:
                tokens.append(op_match.group())
                i += len(op_match.group()) 
                continue
            id_match = identifier_re.match(expression[i:])
            if id_match:
                tokens.append(id_match.group())
                i += len(id_match.group())
                continue
            if char in ' \n':
                i += 1
                continue
            raise Exception(f"ERROR: Token Error '{char}' is not a valid token, input file is not in BNF")
        return tokens

    def tokenize_dpll(self, expression):
        tokens = []
        i = 0
        while i < len(expression):
            char = expression[i]
            if char in ['!', '&', '(', ')']:
                tokens.append(char)
                i += 1
                continue
            elif char.isalnum() or char == '_':
                start = i
                while i < len(expression) and (expression[i].isalnum() or expression[i] == '_'):
                    i += 1
                tokens.append(expression[start:i])
                next_char_index = i
                while next_char_index < len(expression) and expression[next_char_index] == ' ':
                    next_char_index += 1
                if next_char_index < len(expression) and expression[next_char_index] not in [')', '&']:
                    tokens.append('|')
                continue
            elif char == ' ':
                i += 1
                continue
            else:
                raise Exception(f"ERROR: Token Error '{char}' is not a valid token, input file is not in CNF")
        return tokens

if __name__ == "__main__":
    try:
        parser = argparse.ArgumentParser(description="DPLL solver for BNF and CNF sentences.")
        parser.add_argument("-v", action="store_true", required=False, help="Enable verbose output for the DPLL solver.")
        parser.add_argument("-mode", choices=["cnf", "dpll", "solver"], required=True, help="Mode of the solver: cnf, dpll, solver.")
        parser.add_argument("input_file", help="Path to the input file with CNF or BNF sentences.")
        args = parser.parse_args()
        
        input_Processor = InputProcessor()
        verbose = args.v
        mode = args.mode
        expression = input_Processor.get_input_from_file(args.input_file)
        tokens = input_Processor.tokenize_dpll(expression) if mode == 'dpll' else input_Processor.tokenize_cnf(expression)
        parser = Parser(tokens)
        root = parser.parse()
        cnf_converter = CNFConverter(root)
        
        if mode in ['cnf', 'solver']:
            cnf_converter.bnf_to_cnf()
            if mode == 'cnf':
                clauses = cnf_converter.get_clauses(root)
                print("CNF sentences:")
                for clause in clauses:
                    print(" ".join(clause))

        if mode in ['solver', 'dpll']:
            dpll_solver = DPLLSolver(verbose)
            if not cnf_converter.is_cnf(root):
                raise Exception("ERROR: input file is not in CNF")
            clauses = cnf_converter.get_clauses(root)
            for clause in clauses:
                print(" ".join(clause))
            success, solution = dpll_solver.solve_dpll(clauses)
            if success:
                print("Solution:")
                for var, val in sorted(solution.items()):
                    print(f"{var}={val}")
            else:
                print("\nNO SOLUTION")

    except Exception as e:
        print(f"{e}")
        sys.exit(1)