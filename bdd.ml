type expr =
    | ATOM of char
    | NOT of expr
    | AND of expr * expr
    | OR of expr * expr
    | IMPLIES of expr * expr
    | BIIMPLIES of expr * expr
    | TRUE
    | FALSE


let exercise_45a = BIIMPLIES (
    NOT (AND (ATOM 'P', ATOM 'Q')),
    OR (NOT (ATOM 'P'), NOT (ATOM 'Q'))
)
let example_34 = IMPLIES (
    OR (ATOM 'P', ATOM 'Q'),
    OR (ATOM 'Q', ATOM 'R')
)


type bdd =
    | TRUE
    | FALSE
    | IF of char * bdd * bdd (* if ATOM char then bdd else bdd *)


type unary_op = NOT
type binary_op = AND | OR | IMPLIES | BIIMPLIES
type bdd_expr =
    | UNARY of unary_op * bdd
    | BINARY of binary_op * bdd * bdd


let rec invert = function
    | TRUE         -> FALSE
    | FALSE        -> TRUE
    | IF (p, x, y) -> IF (p, invert x, invert y)


let rec simplify = function
    | UNARY (NOT, bdd)     -> invert bdd
    | BINARY (op, z1, z2) -> (
        if z1 = z2 then z1
        else match (z1, z2) with
        | (TRUE, _)                          -> (
                match op with
                | AND       -> z2
                | OR        -> TRUE
                | IMPLIES   -> z2
                | BIIMPLIES -> z2
        )
        | (_, TRUE)                          -> (
                match op with
                | AND       -> z1
                | OR        -> TRUE
                | IMPLIES   -> TRUE
                | BIIMPLIES -> z1
        )
        | (FALSE, _)                         -> (
                match op with
                | AND       -> FALSE
                | OR        -> z2
                | IMPLIES   -> TRUE
                | BIIMPLIES -> invert z2
        )
        | (_, FALSE)                         -> (
                match op with
                | AND       -> FALSE
                | OR        -> z1
                | IMPLIES   -> invert z1
                | BIIMPLIES -> invert z1
        )
        | (IF (p1, x1, y1), IF (p2, x2, y2)) ->
                if p1 = p2 then IF (
                    p1,
                    simplify (BINARY (op, x1, x2)),
                    simplify (BINARY (op, y1, y2))
                )
                else if p1 < p2 then IF (
                    p1,
                    simplify (BINARY (op, x1, z2)),
                    simplify (BINARY (op, y1, z2))
                )
                else IF (
                    p2,
                    simplify (BINARY (op, x2, z1)),
                    simplify (BINARY (op, y2, z1))
                )
    )


let rec to_bdd = function
    | ATOM x             -> IF (x, TRUE, FALSE)
    | NOT e              -> simplify (UNARY (NOT, to_bdd e))
    | AND (e1, e2)       -> simplify (BINARY (AND, to_bdd e1, to_bdd e2))
    | OR (e1, e2)        -> simplify (BINARY (OR, to_bdd e1, to_bdd e2))
    | IMPLIES (e1, e2)   -> simplify (BINARY (IMPLIES, to_bdd e1, to_bdd e2))
    | BIIMPLIES (e1, e2) -> simplify (BINARY (BIIMPLIES, to_bdd e1, to_bdd e2))
    | TRUE               -> TRUE
    | FALSE              -> FALSE


let rec exec bdd l =
    match bdd with
    | TRUE         -> true
    | FALSE        -> false
    | IF (p, x, y) ->
            let rec find a = function
                | (k, v)::t -> if k = a then v else find a t
                | [] -> failwith "No such key"
            in
                if find p l then exec x l else exec y l


open Printf

let pp e =
    let rec pp_bdd ppf = function
        | TRUE         -> fprintf ppf "1"
        | FALSE        -> fprintf ppf "0"
        | IF (p, x, y) -> fprintf ppf "@[<v>%c@[<v 1>@;+ %a@;- %a@]@]" p pp_bdd x pp_bdd y
    in fprintf stdout "%a\n" pp_bdd e


let to_dot bdd =
    let rec dotify n = function
        | TRUE         -> sprintf "\t_%i [label=\"1\", shape=square];" n
        | FALSE        -> sprintf "\t_%i [label=\"0\", shape=square];" n
        | IF (p, x, y) -> 
                let def = sprintf "\t_%i [label=\"%c\"];" n p in
                let nx = n * 2 + 1 in
                let ny = n * 2 + 2 in
                let defx = dotify nx x in
                let defy = dotify ny y in
                let edgex = sprintf "\t_%i -> _%i;" n nx in
                let edgey = sprintf "\t_%i -> _%i [style=dotted];" n ny in
                    sprintf "%s\n%s\n%s\n%s\n%s" def defx defy edgex edgey
    in sprintf "digraph bdd {\n%s\n}" (dotify 0 bdd)


let export bdd filename =
    let oc = open_out filename in
        fprintf oc "%s\n" (to_dot bdd);
        close_out oc
