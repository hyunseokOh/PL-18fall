type exp = X
		  | INT of int
		  | REAL of float
		  | ADD of exp * exp
		  | SUB of exp * exp
		  | MUL of exp * exp
		  | DIV of exp * exp
		  | SIGMA of exp * exp * exp
		  | INTEGRAL of exp * exp * exp

exception FreeVariable

let rec calculate : exp -> float = fun(e) ->
	let rec calPoly : exp -> float list = fun(e) ->
		match e with
		| X -> 0.0::1.0::[]
		| INT num -> float_of_int(num)::[]
		| REAL num -> num::[]
		| ADD (e1,e2) ->
			let rec sumList = fun(l1,l2) ->
				match l1 with
				| [] -> l2
				| x::l3 -> (match l2 with
							| [] -> l1
							| y::l4 -> (x+.y)::sumList(l3,l4))
			in

			sumList(calPoly(e1),calPoly(e2))

		| SUB (e1,e2) ->
			let rec subList = fun(l1,l2) ->
				match l2 with
				| [] -> l1
				| y::l4 -> (match l1 with
							| [] -> (-y)::subList([],l4)
							| x::l3 -> (x-.y)::subList(l3,l4) 
	
		| 
	
		| MUL (e1,e2) -> mathemadiga(e1) * mathemadiga(e2)
	| DIV (e1,e2) -> mathemadiga(e1) / mathemadiga(e2)
	| SIGMA (e1,e2,e3) ->
	| INTEGRAL (e1,e2,e3) ->
