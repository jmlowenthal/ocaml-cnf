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


let expr_a = AND(IMPLIES(ATOM('P'), ATOM('Q')), IMPLIES(ATOM('Q'), ATOM('P')))
let expr_b = AND(OR(AND(ATOM('P'), ATOM('Q')), ATOM('R')), NOT(OR(ATOM('P'), ATOM('Q'))))
let expr_c = OR (NOT (AND (ATOM 'P', AND (ATOM 'Q', ATOM 'R'))), OR (AND (ATOM 'P', ATOM 'Q'), ATOM 'R'))
let expr_x = OR(TRUE, FALSE)
let expr_y = OR(OR(AND(ATOM 'A', ATOM 'B'), ATOM 'C'), ATOM 'D')
let expr_z = OR(OR(AND(ATOM('A'), ATOM('B')), AND(ATOM('C'), ATOM('D'))), ATOM('E'))


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


let rec is_in x = function
    | []                   -> false
    | h :: t               -> if h = x then true else is_in x t


let rec list_trim term = function
    | []                       -> []
    | h :: t                   ->
            if h = term then list_trim term t
            else h :: (list_trim term t)


type expr_list =
    | AND_LIST of expr_list list
    | OR_LIST of expr_list list
    | EXPR of expr

exception Exception of string

let listify expr =
    let rec listificate e = function
        | AND_LIST l               -> (
                match e with
                | AND(e1, e2)      -> listificate e2 (listificate e1 (AND_LIST l))
                | OR(e1, e2)       -> AND_LIST((listificate e (OR_LIST [])) :: l)
                | _                -> AND_LIST((EXPR e)::l)
          )
        | OR_LIST l                -> (
                match e with
                | OR(e1, e2)       -> listificate e2 (listificate e1 (OR_LIST l))
                | AND(e1, e2)      -> OR_LIST((listificate e (AND_LIST [])) :: l)
                | _                -> OR_LIST((EXPR e)::l)
          )
        | _                        -> raise (Exception "Oops")
    in match expr with
    | AND(e1, e2)                  -> listificate expr (AND_LIST [])
    | OR(e1, e2)                   -> listificate expr (OR_LIST [])
    | _                            -> EXPR(expr) 


let rec treeify = function
    | AND_LIST [e]                 -> treeify e
    | OR_LIST [e]                  -> treeify e
    | AND_LIST (h :: t)            -> AND (treeify h, treeify (AND_LIST t))
    | OR_LIST (h :: t)             -> OR (treeify h, treeify (OR_LIST t))
    | EXPR e                       -> e
    | _                            -> raise (Exception "Oops")


let cnf e = dis(neg(impl(e)))


let simplify e = 
    let rec collate = function
        | AND_LIST [h]             -> h
        | AND_LIST (EXPR(FALSE) :: _)    -> EXPR(FALSE)
        | AND_LIST (EXPR(TRUE) :: t)     -> collate (AND_LIST t)
        | AND_LIST (h :: t)        ->
                let h_inv = EXPR (NOT (treeify h)) in
                    if is_in h_inv t then EXPR(FALSE)
                    else if is_in h t then collate (AND_LIST t)
                    else listify(AND(treeify h, treeify (collate (AND_LIST t))))
        | OR_LIST [h]              -> h
        | OR_LIST (EXPR(FALSE) :: t)     -> collate (OR_LIST t)
        | OR_LIST (EXPR(TRUE) :: _)      -> EXPR(TRUE)
        | OR_LIST (h :: t)         ->
                let h_inv = EXPR (NOT (treeify h)) in
                    if is_in h_inv t then EXPR(TRUE)
                    else if is_in h t then collate (OR_LIST t)
                    else listify(OR(treeify h, treeify (collate (OR_LIST t))))
        | e                        -> e
    in let simplificate = function
        | AND_LIST l               -> collate (AND_LIST (List.map collate l))
        | OR_LIST l                -> collate (OR_LIST (List.map collate l))
    in treeify (simplificate (listify (cnf e)))


open Format


let pp e = 
    let rec pp_expr ppf = function
        | ATOM(x)              -> fprintf ppf "%c" x
        | NOT(e)               -> fprintf ppf "¬%a" pp_expr e
        | AND(e1, e2)          -> fprintf ppf "(%a ∧ %a)" pp_expr e1 pp_expr e2
        | OR(e1, e2)           -> fprintf ppf "(%a ∨ %a)" pp_expr e1 pp_expr e2
        | IMPLIES(e1, e2)      -> fprintf ppf "(%a → %a)" pp_expr e1 pp_expr e2
        | BIIMPLIES(e1, e2)    -> fprintf ppf "(%a ↔ %a)" pp_expr e1 pp_expr e2
        | TRUE                 -> fprintf ppf "true"
        | FALSE                -> fprintf ppf "false"
    in fprintf std_formatter "%a\n" pp_expr e


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

