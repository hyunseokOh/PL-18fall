module type Queue =
	sig
		type element
		type queue
		exception EMPTY_Q
		val emptyQ: queue
		val enQ: queue * element -> queue
		val deQ: queue -> element * queue
	end

module IntListQ = 
	struct
		type element = int list
		type queue = ((int list list) * (int list list))
		exception EMPTY_Q
		let emptyQ = ([],[])
		let enQ(q,x) = match q with
            | (l1,l2) -> (x::l1,l2)
			
        let deQ q =
            let rec clean l1 l2 = match (l1,l2) with
				| ([],[]) -> raise EMPTY_Q
				| (hd::tl,_) -> clean tl (hd::l2)
                | ([],hd::tl) -> (hd,([],tl))
			in

			match q with
			| (l,[]) -> clean l []
            | (l,x::ll) -> (x,(l,ll))
	end

module ValidIntListQ = (IntListQ : Queue)
