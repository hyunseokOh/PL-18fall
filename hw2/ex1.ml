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

let rec calculate e =
	let rec evalPoly e x =
		match e with
		| X -> x
		| INT num -> float_of_int(num)
		| REAL num -> num
		| ADD (e1,e2) -> evalPoly e1 x +. evalPoly e2 x
		| SUB (e1,e2) -> evalPoly e1 x -. evalPoly e2 x
		| MUL (e1,e2) -> evalPoly e1 x *. evalPoly e2 x
	    | DIV (e1,e2) -> evalPoly e1 x /. evalPoly e2 x
        | SIGMA (e1,e2,e3) -> 
                let v1 = int_of_float(evalPoly e1 x) in
                let v2 = int_of_float(evalPoly e2 x) in
                if v1 > v2 then 0.0
                else (evalPoly e3 (float_of_int(v1))) +. (evalPoly (SIGMA(ADD(e1,INT 1),e2,e3)) x)
        | INTEGRAL (e1,e2,e3) ->
                let v1 = evalPoly e1 x in
                let v2 = evalPoly e2 x in
                if v1-.v2<0.1 || v2-.v1<0.1 then 0.0
                else if v1>v2 then (evalPoly (INTEGRAL(e2,e1,e3)) x) *. -1.0
                     else 0.1*.(evalPoly e3 v1) +. (evalPoly (INTEGRAL(ADD(e1,REAL 0.1),e2,e3)) x) 

    in

    match e with
    | X -> raise FreeVariable
    | INT num -> float_of_int(num)
    | REAL num -> num
    | ADD (e1,e2) -> calculate e1 +. calculate e2
    | SUB (e1,e2) -> calculate e1 -. calculate e2
    | MUL (e1,e2) -> calculate e1 *. calculate e2
    | DIV (e1,e2) -> calculate e1 /. calculate e2
    | SIGMA (e1,e2,e3) ->
            let v1 = int_of_float(calculate e1) in
            let v2 = int_of_float(calculate e2) in
            if v1  > v2 then 0.0
            else (evalPoly e3 (float_of_int(v1))) +. (calculate (SIGMA(ADD(e1,INT 1),e2,e3)))
    | INTEGRAL (e1,e2,e3) ->
            let v1 = calculate e1 in
            let v2 = calculate e2 in
            if v1-.v2 < 0.1 || v2-.v1<0.1 then 0.0
            else if v1>v2 then (calculate (INTEGRAL(e2,e1,e3))) *. -1.0
                 else 0.1*.(evalPoly e3 v1) +. (calculate (INTEGRAL(ADD(e1,REAL 0.1),e2,e3)))


