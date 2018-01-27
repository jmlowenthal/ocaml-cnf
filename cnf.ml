(*
 * A CNF reducer                                                      25/01/2018
 * 
 * function cnf : expr -> expr
 * > Reduces an expression to conjunctive normal form
 *
 * function pp : expr -> unit
 * > Pretty prints the expression
 *
 * expr_a = ((P → Q) ^ (Q → P))
 * expr_b = (((P ^ Q) v R) ^ ¬(P v Q))
 * expr_z = (((A ^ B) v (C ^ D)) v E)
 *
 * Other expression can be created using prefix notation. Consult `type expr`
 * for a list of possible AST nodes.
 *
 *)

type expr =
    | ATOM of char
    | NOT of expr
    | AND of expr * expr
    | OR of expr * expr
    | IMPLIES of expr * expr
    | BIIMPLIES of expr * expr
    | TRUE
    | FALSE


exception LexingError of int * string

let lexer stream =
    let rec lex pos stream =
        let prefix str =
            let rec prfx i =
                if pos + i < (String.length stream)
                   && i < (String.length str)
                   && stream.[pos + i] = str.[i] then prfx (i + 1)
                else if i >= (String.length str) then true
                else false
            in prfx 0
        in
        if pos >= (String.length stream) then []
        else if prefix "BIIMPLIES" then
            match lex (pos + 9) stream with
                | a :: b :: t   -> BIIMPLIES(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "IMPLIES" then
            match lex (pos + 7) stream with
                | a :: b :: t   -> IMPLIES(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "FALSE" then FALSE :: (lex (pos + 5) stream)
        else if prefix "TRUE" then TRUE :: (lex (pos + 4) stream)
        else if prefix "AND" then
            match lex (pos + 3) stream with
                | a :: b :: t   -> AND(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "NOT" then
            match lex (pos + 3) stream with
                | a :: t      -> NOT(a) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "OR" then
            match lex (pos + 2) stream with
                | a :: b :: t   -> OR(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix " " then lex (pos + 1) stream
        else ATOM(stream.[pos]) :: (lex (pos + 1) stream)
    in match lex 0 stream with
        | [a]              -> a
        | _                -> raise (LexingError (0, "Multiple expressions found"))


let rec impl = function
    | IMPLIES(e1, e2)      -> OR(NOT(impl(e1)), impl(e2))
    | BIIMPLIES(e1, e2)    -> AND(impl(IMPLIES(e1, e2)), impl(IMPLIES(e2, e1)))

    | ATOM(x)              -> ATOM(x)
    | NOT(e)               -> NOT(impl(e))
    | AND(e1, e2)          -> AND(impl(e1), impl(e2))
    | OR(e1, e2)           -> OR(impl(e1), impl(e2))
    | TRUE                 -> TRUE
    | FALSE                -> FALSE


let rec neg = function
    | NOT(AND(e1, e2))     -> OR(neg(NOT(e1)), neg(NOT(e2)))
    | NOT(OR(e1, e2))      -> AND(neg(NOT(e1)), neg(NOT(e2)))
    | NOT(NOT(e))          -> neg(e)

    | ATOM(x)              -> ATOM(x)
    | NOT(e)               -> NOT(neg(e))
    | AND(e1, e2)          -> AND(neg(e1), neg(e2))
    | OR(e1, e2)           -> OR(neg(e1), neg(e2))
    | IMPLIES(e1, e2)      -> IMPLIES(neg(e1), neg(e2))   (* Not expected *)
    | BIIMPLIES(e1, e2)    -> BIIMPLIES(neg(e1), neg(e2)) (* ^^^^^^^^^^^^ *)
    | TRUE                 -> TRUE
    | FALSE                -> FALSE


let rec dis = function
    | OR(e1, AND(e2, e3))  -> AND(dis(OR(e1, e2)), dis(OR(e1, e3)))
    | OR(AND(e1, e2), e3)  -> AND(dis(OR(e1, e3)), dis(OR(e2, e3)))
    | OR(e1, e2)           -> (* I feel like this could be cleaner :/ *)
            let e1' = dis(e1) and e2' = dis(e2) in
                if e1 = e1' && e2 = e2' then OR(e1', e2')
                else dis(OR(e1', e2'))

    | ATOM(x)              -> ATOM(x)
    | NOT(e)               -> NOT(dis(e))
    | AND(e1, e2)          -> AND(dis(e1), dis(e2))
    | IMPLIES(e1, e2)      -> IMPLIES(dis(e1), dis(e2))   (* Not expected *)
    | BIIMPLIES(e1, e2)    -> BIIMPLIES(dis(e1), dis(e2)) (* ^^^^^^^^^^^^ *)
    | TRUE                 -> TRUE
    | FALSE                -> FALSE


let cnf e = dis(neg(impl(e)))

open Format

let rec pp_expr ppf = function
    | ATOM(x)              -> fprintf ppf "%c" x
    | NOT(e)               -> fprintf ppf "¬%a" pp_expr e
    | AND(e1, e2)          -> fprintf ppf "(%a ^ %a)" pp_expr e1 pp_expr e2
    | OR(e1, e2)           -> fprintf ppf "(%a v %a)" pp_expr e1 pp_expr e2
    | IMPLIES(e1, e2)      -> fprintf ppf "(%a → %a)" pp_expr e1 pp_expr e2
    | BIIMPLIES(e1, e2)    -> fprintf ppf "(%a ↔ %a)" pp_expr e1 pp_expr e2
    | TRUE                 -> fprintf ppf "true"
    | FALSE                -> fprintf ppf "false"

let pp e = fprintf std_formatter "%a\n" pp_expr e

let expr_a = AND(IMPLIES(ATOM('P'), ATOM('Q')), IMPLIES(ATOM('Q'), ATOM('P')))
let expr_b = AND(OR(AND(ATOM('P'), ATOM('Q')), ATOM('R')), NOT(OR(ATOM('P'), ATOM('Q'))))

let expr_z = OR(OR(AND(ATOM('A'), ATOM('B')), AND(ATOM('C'), ATOM('D'))), ATOM('E'))
