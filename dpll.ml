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
let expr_24 = IMPLIES (
    AND (
        IMPLIES (ATOM 'Q', ATOM 'R'),
        AND (
            IMPLIES (
                ATOM 'R',
                AND (ATOM 'P', ATOM 'Q')
            ),
            IMPLIES (
                ATOM 'P',
                OR (ATOM 'Q', ATOM 'R')
            )
        )
    ),
    BIIMPLIES (ATOM 'P', ATOM 'Q')
)
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


type clause = CLAUSE of expr list


let clausal e =
    let rec to_exprlist = function
        | []                        -> []
        | (EXPR x) :: t             -> x :: (to_exprlist t)
    in let rec clausify = function
        | AND_LIST []               -> []
        | AND_LIST((EXPR x)::t)     -> 
            let c = clausify (AND_LIST t) in (CLAUSE [x]) :: c
        | AND_LIST((OR_LIST ol)::t) ->
            let c = clausify (AND_LIST t) in (CLAUSE (to_exprlist ol)) :: c
        | e                        -> clausify (AND_LIST [e])
    in clausify (listify (cnf e))


let rec is_taut = function
    | CLAUSE []                   -> false
    | CLAUSE ((NOT h)::t)         -> if is_in h t then true else is_taut (CLAUSE t)
    | CLAUSE (h::t)               -> if is_in (NOT h) t then true else is_taut (CLAUSE t)


let rec setify l =
    let rec setificate = function
        | CLAUSE []               -> CLAUSE []
        | CLAUSE (h::t)           ->
                let CLAUSE t' = setificate (CLAUSE t)
                in if is_in h t' then CLAUSE t' else CLAUSE (h::t')
    in match l with
        | []                      -> []
        | h::t                    ->
                let t' = setify t
                in if is_in h t' then t' else h::t'


let rec unit_prop al =
    let rec prop = function
        | (l, [])              -> l
        | (l, ((CLAUSE [x])::t)) ->
            let rec rem_containers = function
                | []           -> []
                | (CLAUSE h)::t         ->
                    if is_in x h then rem_containers t
                    else (CLAUSE h) :: (rem_containers t)
            in let rec trim_neg = function
                | []           -> []
                | h::t         -> (
                    match x with
                        | NOT x' -> if h = x' then trim_neg t else h :: (trim_neg t)
                        | _      -> if h = NOT x then trim_neg t else h :: (trim_neg t)
                )
            in let rec trim_neg_all = function
                | []            -> []
                | (CLAUSE h)::t -> (CLAUSE (trim_neg h)) :: (trim_neg_all t)
            in prop (trim_neg_all (rem_containers l), trim_neg_all (rem_containers t))
        | (l, h::t)            -> prop (h::l, t)
    in prop ([], al)


let rec dpll_l al =
    let rec trim_tauts = function
        | []                       -> []
        | h::t                     ->
            if is_taut h then trim_tauts t
            else let t' = trim_tauts t in h :: t'
    in let get_first_atom = function
        | (CLAUSE ((NOT h)::_))::_ -> h
        | (CLAUSE (h::_))::_       -> h
    in let l = trim_tauts (setify al)
    in match l with
        | []                       -> false
        | _                        -> 
            if is_in (CLAUSE []) l then true
            else dpll_l (unit_prop ((CLAUSE [get_first_atom l])::l))
                && dpll_l (unit_prop ((CLAUSE [NOT (get_first_atom l)])::l))


let dpll e = dpll_l (clausal (NOT e))


open Format


let rec pp_expr ppf = function
    | ATOM(x)              -> fprintf ppf "%c" x
    | NOT(e)               -> fprintf ppf "¬%a" pp_expr e
    | AND(e1, e2)          -> fprintf ppf "(%a ∧ %a)" pp_expr e1 pp_expr e2
    | OR(e1, e2)           -> fprintf ppf "(%a ∨ %a)" pp_expr e1 pp_expr e2
    | IMPLIES(e1, e2)      -> fprintf ppf "(%a → %a)" pp_expr e1 pp_expr e2
    | BIIMPLIES(e1, e2)    -> fprintf ppf "(%a ↔ %a)" pp_expr e1 pp_expr e2
    | TRUE                 -> fprintf ppf "true"
    | FALSE                -> fprintf ppf "false"


let rec pp_clauseset ppf e =
    let rec pp_clause ppf' l = 
        match l with
            | []               -> fprintf ppf' ""
            | [x]              -> fprintf ppf' "%a" pp_expr x
            | (h::t)           -> fprintf ppf' "%a, %a" pp_expr h pp_clause t
    in match e with
        | []               -> fprintf ppf ""
        | (CLAUSE l)::t    -> fprintf ppf "{ %a } %a" pp_clause l pp_clauseset t


let pp_e e = fprintf std_formatter "%a\n" pp_expr e
let pp_c e = fprintf std_formatter "%a\n" pp_clauseset e 


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

