type expr = NUM of int
			| PLUS of expr * expr
			| MINUS of expr * expr

type formula = TRUE
			  | FALSE
			  | NOT of formula
			  | ANDALSO of formula * formula
			  | ORELSE of formula * formula
			  | IMPLY of formula * formula
			  | LESS of expr * expr

let rec expr2num : expr -> int = fun(e) ->
	match e with
	| NUM num -> num
	| PLUS (e1,e2) -> expr2num(e1)+expr2num(e2)
	| MINUS (e1,e2) -> expr2num(e1)-expr2num(e2)

let rec eval : formula -> bool = fun(f) ->
	match f with 
	| TRUE -> true 
	| FALSE -> false
	| NOT p -> not(eval(p))
	| ANDALSO (p,q) -> eval(p) && eval(q)
	| ORELSE  (p,q) -> eval(p) || eval(q)
	| IMPLY   (p,q) -> not(eval(p)) || eval(q)
	| LESS  (e1,e2) -> 
		if expr2num(e1) < expr2num(e2) then true
		else false

