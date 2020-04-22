from lark import Lark, Transformer
import z3

try:
    input = raw_input   # For Python2 compatibility
except NameError:
    pass

class Z3OutputHandler(Transformer):
    z3_output_grammar = r"""
        ?output_lst: (output)+ -> mk_lst

        ?output: result (err_message)? -> mk_res
        
        ?result: SAT model -> mk_sat
            | UNSAT -> mk_unsat
            | UNK -> mk_unknown
        
        ?err_message: OPAREN ERR STRING CPAREN

        ?model: OPAREN MODEL sols CPAREN -> mk_model

        ?sols: (sol)+ -> mk_lst

        ?sol: OPAREN DEFFUN ID OPAREN CPAREN sort value CPAREN -> mk_sol

        ?sort: (INTSORT | REALSORT | BOOLSORT)

        ?bool_val: (TRUE | FALSE)

        ?value: prim_val -> mk_prim_val
            | TOINT prim_val -> mk_toint_prim_val
            | MULT value value
            | OPAREN value CPAREN -> mk_paren

        ?prim_val: INT -> mk_int_val
            | bool_val -> mk_bool_val
            | OPAREN prim_val CPAREN -> mk_paren
            | MINUS prim_val -> mk_neg

        MODEL: "model"
        SAT: "sat"
        UNSAT: "unsat"
        UNK: "unknown"
        ERR: "error"
        OPAREN: "("
        CPAREN: ")"
        DEFFUN: "define-fun"
        TOINT: "to_int"
        INTSORT: "Int"
        REALSORT: "Real"
        BOOLSORT: "Bool"
        MINUS: "-"
        DIV: "/"
        MULT: "*"
        TRUE: "true"
        FALSE: "false"
        COMMENT: ";" /[^\n]/*
        %import common.CNAME -> ID
        %import common.INT -> INT
        %import common.ESCAPED_STRING -> STRING
        %import common.WS
        %ignore WS
        %ignore COMMENT
        """

    def mk_res(self, args):
        return args[0]

    # def pr_err_message(self, (oparen, err, msg, cparen)):
    #     print msg

    def mk_sat(self, tokens):
        (sat, model) = tokens
        return (z3.sat, model)

    mk_unsat = lambda self, _: (z3.unsat, None)

    mk_unknown = lambda self, _: (z3.unknown, None)

    def mk_model(self, tokens):
        (oparen, model, sols, cparen) = tokens
        return sols

    def mk_lst(self, lst):
        return lst

    def mk_sol(self, tokens):
        (oparen1, deffun, id, oparen2, cparen2, sort, value, cparen1) = tokens
        return (str(id) , value)

    def mk_paren(self, tokens):
        (oparen, e, cparen) = tokens
        return e

    def mk_prim_val(self, tokens):
        (e,) = tokens
        return e

    def mk_toint_prim_val(self, tokens):
        (toint, e) = tokens
        return e

    def mk_int_val(self, tokens):
        (i,) = tokens
        return int(i)

    def mk_bool_val(self, tokens):
        (i,) = tokens
        return bool(i)

    def mk_neg(self, tokens):
        (minus, e) = tokens
        return -e

    parser = Lark(z3_output_grammar, start='output', lexer='dynamic_complete')

