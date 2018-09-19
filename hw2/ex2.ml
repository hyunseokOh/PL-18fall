type ae = CONST of int
	    | VAR of string
	    | POWER of string * int
		| TIMES of ae list
		| SUM of ae list

exception InvalidArgument

let rec diff: ae * string -> ae = fun(exp,var) -> match exp with
	| CONST _ -> CONST 0
	| VAR s -> if s=var then CONST 1
		       else CONST 0
	| POWER (s,n) -> if s=var then
                        (if n==0 then CONST 0
                         else if n==1 then CONST 1
                         else if n==2 then TIMES(CONST 2 :: VAR s ::[])
                         else TIMES ((CONST n)::(POWER (s,n-1))::[]))
                     else CONST 0
    | TIMES l ->
            let rec diffTim ll var =
                match ll with
                | [] -> CONST 0
                | hd::[] -> diff(hd,var)
                | CONST 0::tl -> CONST 0
                | CONST x::tl -> TIMES(CONST x::(diffTim tl var)::[])
                | hd::tl -> SUM(TIMES ((diff(hd,var))::tl)::TIMES (hd::(diffTim tl var)::[])::[])
            in
            
           (match l with 
                  | [] -> raise InvalidArgument
                  | hd::[] -> diff(hd,var)
                  | _ -> (diffTim l var)) 
    | SUM l -> 
            let rec diffSum ll var =
                match ll with
                | [] -> []
                | (CONST _)::tl -> diffSum tl var
                | hd::tl -> (diff(hd,var))::((diffSum tl var))
            in

            (match l with
                | [] -> raise InvalidArgument
                | hd::[] -> diff(hd,var)
                | _  -> SUM (diffSum l var))
