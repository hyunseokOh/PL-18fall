let rec sigma : int * int * (int -> int) -> int = fun (x,y,f) ->
	if x>y then 0
	else sigma(x+1,y,f)+f(x)
