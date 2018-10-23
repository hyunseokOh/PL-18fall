type require = id * (cond list)
and cond = Items of gift list
         | Same of id
         | Common of cond * cond
         | Except of cond * gift list
and gift = int
and id = A | B | C | D | E

(* shoppingList : require list -> (id * gift list) list *)
let shoppingList reqlst = 
    let result = (A,[])::(B,[])::(C,[])::(D,[])::(E,[])::[] in
    let rec iterUpdate reqlst result =

        let rec personUpdate clst lst result = 
        
            let rec insert l_init l_new = match l_new with
                                         | [] -> l_init
                                         | hd::tl -> if (List.mem hd l_init) then insert l_init tl
                                                     else insert (hd::l_init) tl
            in

            let rec delete l_init l_del = match l_del with
                                         | [] -> l_init
                                         | hd::tl -> if (List.mem hd l_init) then 
                                                        delete (List.filter (fun x -> x<>hd) l_init) tl
                                                     else delete l_init tl
            in

            let rec itemUpdate cnd lst result = match cnd with
                 | Items gl -> insert lst gl 
                 | Same id -> (match id with 
                                | A -> insert lst (snd (List.nth result 0))
                                | B -> insert lst (snd (List.nth result 1))
                                | C -> insert lst (snd (List.nth result 2))
                                | D -> insert lst (snd (List.nth result 3))
                                | E -> insert lst (snd (List.nth result 4))
                              )
                 | Common (c1,c2) -> 
                         let lst1 = itemUpdate c1 lst result in
                         let lst2 = itemUpdate c2 lst result in
                         List.filter (fun x -> List.mem x lst2) lst1
                        
                 | Except (c1,gl) -> 
                         let lst1 = itemUpdate c1 lst result in
                         delete lst1 gl
            in

            match clst with 
            | [] -> lst
            | hd::tl ->
                    let lst1=itemUpdate hd lst result in
                    List.sort compare (personUpdate tl lst1 result)
                    
        in
    
        let rec resultUpdate tup result = match result with
                                        | [] -> []
                                        | hd::tl -> (match (fst tup, fst hd) with
                                                    | (A,A) -> tup::resultUpdate tup tl
                                                    | (B,B) -> tup::resultUpdate tup tl
                                                    | (C,C) -> tup::resultUpdate tup tl
                                                    | (D,D) -> tup::resultUpdate tup tl
                                                    | (E,E) -> tup::resultUpdate tup tl
                                                    | (_,_) -> hd::resultUpdate tup tl
                                                    )
        in

    match reqlst with
    | [] -> result
    | hd::tl -> (match hd with
                 | (A,clst) -> 
                         let lst1 = personUpdate clst (snd (List.nth result 0)) result in
                         let result1=resultUpdate (A,lst1) result in
                         iterUpdate tl result1
                 | (B,clst) ->
                         let lst1 = personUpdate clst (snd (List.nth result 1)) result in
                         let result1=resultUpdate (B,lst1) result in
                         iterUpdate tl result1
                 | (C,clst) ->
                         let lst1 = personUpdate clst (snd (List.nth result 2)) result in
                         let result1=resultUpdate (C,lst1) result in
                         iterUpdate tl result1
                 | (D,clst) ->
                         let lst1 = personUpdate clst (snd (List.nth result 3)) result in
                         let result1=resultUpdate (D,lst1) result in
                         iterUpdate tl result1
                 | (E,clst) ->
                         let lst1 = personUpdate clst (snd (List.nth result 4)) result in
                         let result1=resultUpdate (E,lst1) result in
                         iterUpdate tl result1
                )
    in

    let result1=iterUpdate reqlst result in
    let result2=iterUpdate reqlst result1 in
    let result3=iterUpdate reqlst result2 in
    let result4=iterUpdate reqlst result3 in
    let result5=iterUpdate reqlst result4 in
    result5
