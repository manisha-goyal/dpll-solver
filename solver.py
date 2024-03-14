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
            raise Exception(f"Expected token '{token_value}', but found '{self.current_token}'")

    def parse(self):
        if self.current_token == '':
            return None
        result = self.expression()
        if self.current_token != '':
            raise Exception("Unexpected end of input: possibly due to unmatched opening parentheses or extraneous input.")
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

    def remove_equivalences(self, node):
        if isinstance(node, Iff):
            node.left = self.remove_equivalences(node.left)
            node.right = self.remove_equivalences(node.right)
            return And(Implies(node.left, node.right), Implies(node.right, node.left))
        elif isinstance(node, (And, Or)):
            node.left = self.remove_equivalences(node.left)
            node.right = self.remove_equivalences(node.right)
        elif isinstance(node, Not):
            node.expr = self.remove_equivalences(node.expr)
        elif isinstance(node, Atom):
            return node
        return node

    def remove_implications(self, node):
        if isinstance(node, Implies):
            return Or(Not(self.remove_implications(node.left)), self.remove_implications(node.right))
        elif isinstance(node, (And, Or)):
            node.left = self.remove_implications(node.left)
            node.right = self.remove_implications(node.right)
        elif isinstance(node, Not):
            node.expr = self.remove_implications(node.expr)
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

    def convert_to_cnf(self):
        self.root = self.remove_equivalences(self.root)
        self.root = self.remove_implications(self.root)
        self.root = self.to_negation_normal_form(self.root)
        while not self.is_cnf(self.root):
            self.root = self.distribution(self.root)
        return self.root

    def print_cnf_clauses(self, node=None):
        if node is None:
            node = self.root
        clauses = self.collect_clauses(node)
        for clause in clauses:
            print(" ".join(clause))

    def collect_literals(self, node):
        if isinstance(node, Or):
            return self.collect_literals(node.left) + self.collect_literals(node.right)
        elif isinstance(node, Not):
            return [f"!{node.expr.name}"]
        elif isinstance(node, Atom):
            return [node.name]
        return []

    def collect_clauses(self, node):
        if isinstance(node, And):
            return self.collect_clauses(node.left) + self.collect_clauses(node.right)
        else:
            return [self.collect_literals(node)]
   
def read_expression_from_file(file_name):
    tokens = []
    with open(file_name) as in_file:
        for line in in_file.readlines():
            if line == '\n':
                continue
            l = line
            tokens.append(f"({l.strip()})")
    return " & ".join(tokens)

def tokenize(expression):
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

        raise Exception(f"ERROR: Token Error '{char}' is not a valid token.")

    return tokens

if __name__ == "__main__":
    try:
        parser = argparse.ArgumentParser(description="DPLL solver for BNF and CNF sentences.")
        parser.add_argument("-v", action="store_true", required=False, help="Enable verbose output for the DPLL solver.")
        parser.add_argument("-mode", choices=["cnf", "dpll", "solver"], required=True, help="Mode of the solver: cnf, dpll, solver")
        parser.add_argument("input_file", help="Path to the input file with CNF or BNF sentences")
        args = parser.parse_args()
        
        verbose = args.v
        mode = args.mode
        expression = read_expression_from_file(args.input_file)
        
        tokens = tokenize(expression)

        parser = Parser(tokens)
        root = parser.parse()
        cnf_converter = CNFConverter(root)

        if mode in ['cnf', 'solver']:
            cnf_converter.convert_to_cnf()
            if mode == 'cnf':
                print("CNF:")
                cnf_converter.print_cnf_clauses() 
                print()
        if mode in ['solver', 'dpll']:
            if not cnf_converter.is_cnf(root):
                raise Exception("ERROR: input file is not in CNF")
            print("\nSolution:\n")
            #dpll_solver(root)
    except Exception as e:
        print(f"{e}", file=sys.stderr)
        sys.exit(1)
