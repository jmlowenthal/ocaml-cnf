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


type node =
    | TRUE
    | FALSE
    | IF of char * int * int


type bdd = node list


type unary_op = NOT
type binary_op = AND | OR | IMPLIES | BIIMPLIES
type bdd_expr =
    | UNARY of unary_op * bdd
    | BINARY of binary_op * bdd * bdd


let rec invert = function
    | []         -> []
    | TRUE :: t  -> FALSE :: (invert t)
    | FALSE :: t -> TRUE :: (invert t)
    | h :: t     -> h :: (invert t)


let rec remove_head n l =
    if n = 0 then l
    else match l with
    | h :: t -> remove_head (n - 1) t
    | _      -> failwith "Not enough items"


let rec is_in x = function
    | [] -> false
    | h :: t -> (h = x) || (is_in x t)


let find item lst =
    let rec finder index = function
        | h :: t -> if h = item then index else finder (index + 1) t
        | [] -> failwith "Not found"
    in finder 0 lst


let rec length = function
    | []   -> 0
    | _::t -> 1 + (length t)


let rec get index lst =
    match (index, lst) with
    | (0, h::_) -> h
    | (n, _::t) -> get (n - 1) t
    | _         -> failwith "Index out of bounds"


(*
 * Returns: (merged DAG as list, key-value list of remappings)
 *)
let rec merge (a, b) =
    match a with
    | []                -> (b, fun _ -> failwith "No mapping")
    | h :: t -> 
            let (t', map) = merge (t, b) in
            match h with
            | IF (p, x, y) ->
                    let remap a = find (get a t) t'
                    in IF (p, remap x, remap y) :: t', 0
            | _            -> 
                    if (is_in h t') then (t', ((* TODO *)))
                    else (h :: t', map)


let rec simplify = function
    | UNARY (NOT, bdd)     -> invert bdd
    | BINARY (op, z1, z2) -> (
        if z1 = z2 then z1
        else match (z1, z2) with
        | ([], _)                                        -> z2
        | (_, [])                                        -> z1
        | (TRUE::_, _)                                   -> (
                match op with
                | AND       -> z2
                | OR        -> [TRUE]
                | IMPLIES   -> z2
                | BIIMPLIES -> z2
        )
        | (_, TRUE::_)                                   -> (
                match op with
                | AND       -> z1
                | OR        -> [TRUE]
                | IMPLIES   -> [TRUE]
                | BIIMPLIES -> z1
        )
        | (FALSE::_, _)                                  -> (
                match op with
                | AND       -> [FALSE]
                | OR        -> z2
                | IMPLIES   -> [TRUE]
                | BIIMPLIES -> invert z2
        )
        | (_, FALSE::_)                                  -> (
                match op with
                | AND       -> [FALSE]
                | OR        -> z1
                | IMPLIES   -> invert z1
                | BIIMPLIES -> invert z1
        )
        | (IF (p1, x1, y1) :: t1, IF (p2, x2, y2) :: t2) ->
                if p1 = p2 then
                    let x' = simplify (BINARY (op, remove_head x1 t1, remove_head x2 t2)) in
                    let y' = simplify (BINARY (op, remove_head y1 t1, remove_head y2 t2)) in
                    let (xy, n) = merge (x', y') in
                        IF (p1, 0, n) :: xy
                else if p1 < p2 then
                    let x' = simplify (BINARY (op, remove_head x1 t1, z2)) in
                    let y' = simplify (BINARY (op, remove_head y1 t1, z2)) in
                    let (xy, n) = merge (x', y') in
                        IF (p1, 0, n) :: xy
                else
                    let x' = simplify (BINARY (op, z1, remove_head x2 t2)) in
                    let y' = simplify (BINARY (op, z1, remove_head y2 t2)) in
                    let (xy, n) = merge (x', y') in
                        IF (p1, 0, n) :: xy
    )

let rec to_bdd = function
    | ATOM x             -> [IF (x, 0, 1); TRUE; FALSE]
    | NOT e              -> simplify (UNARY (NOT, to_bdd e))
    | AND (e1, e2)       -> simplify (BINARY (AND, to_bdd e1, to_bdd e2))
    | OR (e1, e2)        -> simplify (BINARY (OR, to_bdd e1, to_bdd e2))
    | IMPLIES (e1, e2)   -> simplify (BINARY (IMPLIES, to_bdd e1, to_bdd e2))
    | BIIMPLIES (e1, e2) -> simplify (BINARY (BIIMPLIES, to_bdd e1, to_bdd e2))
    | TRUE               -> [TRUE]
    | FALSE              -> [FALSE]


(*let rec exec bdd l =
    match bdd with
    | TRUE         -> true
    | FALSE        -> false
    | IF (p, x, y) ->
            let rec find a = function
                | (k, v)::t -> if k = a then v else find a t
                | [] -> failwith "No such key"
            in
                if find p l then exec x l else exec y l*)


open Printf


let to_dot bdd =
    let rec dotify n = function
        | []                -> ""
        | TRUE :: t         -> 
                (sprintf "\t_%i [label=\"1\", shape=square];\n" n) ^ (dotify (n + 1) t)
        | FALSE :: t        ->
                (sprintf "\t_%i [label=\"0\", shape=square];\n" n) ^ (dotify (n + 1) t)
        | IF (p, x, y) :: t -> 
                let def = sprintf "\t_%i [label=\"%c\"];" n p in
                let edgex = sprintf "\t_%i -> _%i;" n (n + x + 1) in
                let edgey = sprintf "\t_%i -> _%i [style=dotted];" n (n + y + 1) in
                     (sprintf "%s\n%s\n%s\n" def edgex edgey)  ^ (dotify (n + 1) t)
    in sprintf "digraph bdd {\n%s\n}" (dotify 0 bdd)


let export bdd filename =
    let oc = open_out filename in
        fprintf oc "%s\n" (to_dot bdd);
        close_out oc
