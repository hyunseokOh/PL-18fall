type ae = CONST of int
	    | VAR of string
	    | POWER of string * int
		| TIMES of ae list
		| SUM of ae list

exception InvalidArgument

let rec diff: ae * string -> ae = fun(exp,var) ->
	match exp with
	| CONST _ -> CONST 0
	| VAR s -> if s==var then CONST 1
		       else CONST 0
	| POWER (s,n) -> if s==var then
						(if n==0 then CONST 0
    | TIMES l1
