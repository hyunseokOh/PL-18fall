type nat = ZERO | SUCC of nat

let rec natadd : nat * nat -> nat = fun(x,y) -> 
	match x with
	| ZERO -> y
	| SUCC xprev -> (match y with
						| ZERO -> x
						| SUCC yprev ->natadd(xprev,SUCC y))

let rec natmul : nat * nat -> nat = fun(x,y) ->
	match x with
	| ZERO -> ZERO
	| SUCC yprev -> (match y with
						| ZERO -> ZERO
						| SUCC yprev -> natadd(x,natmul(x,yprev)))
