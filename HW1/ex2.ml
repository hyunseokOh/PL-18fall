let rec sumprod : (int * int -> float) * int * int -> float = fun(mm,n,k) ->
	let rec prod : (int * int -> float) * int * int -> float = fun(mm,n,k) ->
		if k<1 then 1.0
		else prod(mm,n,k-1) *. mm(n,k)
	in

	if n<1 then 0.0
	else sumprod(mm,n-1,k) +. prod(mm,n,k)
