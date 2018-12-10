
(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  | TW of var
  | TEq of var
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v
  | TW v
  | TEq v -> [v]

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
    | TW x' -> if (x=x') then (match t with
                | TVar x''
                | TEq x'' -> TW x''
                | _ -> t
                ) else t'
    | TEq x' -> if (x=x') then (match t with
                | TVar x'' -> TEq x'' 
                | _ -> t
               ) else t'
    in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec inclu alp t = match t with
            | TInt | TBool | TString -> false
            | TFun(t1,t2)
            | TPair(t1,t2) -> (inclu alp t1) || (inclu alp t2)
            | TLoc t1 -> inclu alp t1
            | TVar x
            | TW x
            | TEq x -> (x=alp)


let rec unify env (t1,t2) = (* (Typ,Typ) -> Subst *)
    if t1=t2 then empty_subst
    else (match (t1,t2) with    
            | (TFun(tt1,tt2),TFun(tt1',tt2'))
            | (TPair(tt1,tt2),TPair(tt1',tt2')) ->
                let s=unify env (tt1,tt1') in
                let s'=unify env (s tt2,s tt2') in
                s' @@ s
            | (TLoc tt1,TLoc tt1') -> unify env (tt1,tt1')
            | (TVar x,tt)
            | (tt,TVar x) -> if (inclu x tt) then raise (M.TypeError "unify") else (make_subst x tt)

            | (TEq x,tt)
            | (tt,TEq x) -> if (inclu x tt) then raise (M.TypeError "unify")
                            else (match tt with
                            | TInt
                            | TBool
                            | TString
                            | TLoc _
                            | TW _
                            | TEq _ -> make_subst x tt
                            | _ -> raise (M.TypeError "unify")
                            )
            | (TW x,tt)
            | (tt,TW x) -> if (inclu x tt) then raise (M.TypeError "unify")
                           else (match tt with
                           | TInt
                           | TBool
                           | TString
                           | TW _ 
                           | TEq _ -> make_subst x tt
                           | _ -> raise (M.TypeError "unify")
                           )
            | _ -> raise (M.TypeError "unify")
            ) 

let rec expans e = match e with
                    | M.CONST _
                    | M.VAR _
                    | M.FN _ -> false

                    | M.APP (_,_) -> true
                    | M.LET (d,e2) ->(match d with
                            | VAL (_,e1) 
                            | REC (_,_,e1) -> (expans e1) || (expans e2) 
                            )
                    | M.IF (e1,e2,e3) -> 
                            let con=expans e1 in
                            (con && expans e2) || ((not con) && expans e3)
                    | M.BOP (_,e1,e2) -> (expans e1) || (expans e2)
                    | M.READ -> false
                    | M.WRITE e -> expans e
                    | M.MALLOC _ -> true
                    | M.ASSIGN (e1,e2) -> (expans e1) || (expans e2)
                    | M.BANG e -> expans e
                    | M.SEQ (e1,e2) 
                    | M.PAIR (e1,e2) -> (expans e1) || (expans e2)
                    | M.FST e -> expans e
                    | M.SND e -> expans e

let rec malg env exp t = match exp with (* (env,exp,typ) -> subst) *)
     | M.CONST (S s) -> unify env (TString,t)
     | M.CONST (N n) -> unify env (TInt,t)
     | M.CONST (B b) -> unify env (TBool,t)
     | M.VAR x -> 
             let t'=List.assoc x env in
             let tt'=match t' with
                     | SimpleTyp ty -> ty
                     | GenTyp _ ->
                             let buf=subst_scheme empty_subst t' in
                             (match buf with
                             | SimpleTyp _ -> raise (M.TypeError "var")
                             | GenTyp (_,ty) -> ty
                             )
             in
             unify env (t,tt')

     | M.FN (x,e) -> 
             let a1=TVar(new_var ()) in
             let a2=TVar(new_var ()) in
             let s=unify env (TFun(a1,a2),t) in
             let s'=malg ((x,SimpleTyp(s a1))::(subst_env s env)) e (s a2) in
             s' @@ s

     | M.APP (e1,e2) ->
             let a=TVar(new_var ()) in
             let s = malg env e1 (TFun(a,t)) in
             let s'= malg (subst_env s env) e2 (s a) in
             s' @@ s

     | M.LET (d,e2) -> (match d with
            | VAL (x,e1) -> 
                let a = TVar(new_var ()) in
                let s= malg env e1 a in
                let env'=subst_env s env in
                let gt= if (expans e1) then SimpleTyp (s a) else generalize env' (s a) in
                let env''=(x,gt)::env' in
                let s'=malg env'' e2 (s t) in
                s' @@ s

            | REC (f,x,e1) ->
                let a1 = TVar(new_var ()) in
                let a2 = TVar(new_var ()) in
                let a3 = TVar(new_var ()) in
                let env'=(f,SimpleTyp a1)::env in
                let s=unify env' (TFun(a2,a3),a1) in
                let env''=(x,SimpleTyp(s a2))::(subst_env s env') in
                let s'=malg env'' e1 (s a3) in
                let env3=subst_env (s' @@ s) env in
                let env4=(f,generalize env3 (s' (s a1)))::env3 in
                let s''= malg env4 e2 (s' (s t)) in
                s'' @@ (s' @@ s)
 
            )
     
     | M.IF (e1,e2,e3) ->
            let a=TVar(new_var ()) in
            let s=unify env (a,t) in
            let env'=subst_env s env in
            let s'=malg env' e1 TBool in
            let env''=subst_env s' env' in
            let s''=malg env'' e2 (s a) in
            let env2=subst_env s'' env'' in
            let s2=malg env2 e3 (s''(s a)) in
            s2 @@ ( s'' @@ (s' @@ s))

     | M.BOP (b,e1,e2) -> (match b with
            | M.ADD
            | M.SUB ->
                 let s=unify env (TInt,t) in
                 let env'=subst_env s env in
                 let s'=malg env' e1 TInt in
                 let s''=malg (subst_env s' env') e2 TInt in
                 s'' @@ (s' @@ s)
            | M.AND
            | M.OR ->
                 let s=unify env (TBool,t) in
                 let env'=subst_env s env in
                 let s'=malg env' e1 TBool in
                 let s''=malg (subst_env s' env') e2 TBool in
                 s'' @@ (s' @@ s)
            | M.EQ -> 
                 let a1=TEq(new_var ()) in
                 let s=unify env (TBool,t) in
                 let env'=subst_env s env in
                 let s'=malg env' e1 (s a1) in
                 let s''=malg (subst_env s' env') e2 (s' (s a1)) in
                 s'' @@ (s' @@ s)
            
            )

     | M.READ -> unify env (TInt,t)
        
     | M.WRITE e -> 
             let a=TW(new_var ()) in
             let s=unify env (a,t) in
             let s' = malg (subst_env s env) e (s a) in
             s' @@ s
             
     | M.MALLOC e ->
             let a=TVar(new_var ()) in
             let s=unify env (TLoc a,t) in
             let s'=malg (subst_env s env) e (s a) in
             s' @@ s

     | M.ASSIGN (e1,e2) ->
             let s=malg env e1 (TLoc t) in
             let s'=malg (subst_env s env) e2 (s t) in
             s' @@ s
    
     | M.BANG e ->
             malg env e (TLoc t)
     
     | M.SEQ (e1,e2) ->
             let a=TVar(new_var ()) in
             let s=malg env e1 a in
             let s'=malg (subst_env s env) e2 (s t) in
             s' @@ s

     | M.PAIR (e1,e2) ->
             let a1=TVar(new_var ()) in
             let a2=TVar(new_var ()) in
             let s= unify env (TPair(a1,a2),t) in
             let env'=subst_env s env in
             let s'=malg env' e1 (s a1) in
             let s''=malg (subst_env s' env') e2 (s' (s a2)) in
             s'' @@ (s' @@ s)

     | M.FST e ->
             let a1=TVar(new_var ()) in
             let a2=TVar(new_var ()) in

             let s=malg env e (TPair (a1,a2)) in
             let s'=unify (subst_env s env) (t,s a1) in
             s' @@ s
     
     | M.SND e ->
             let a1=TVar(new_var ()) in
             let a2=TVar(new_var ()) in

             let s=malg env e (TPair (a1,a2)) in
             let s'=unify (subst_env s env) (t,s a2) in
             s' @@ s

let rec trans : typ -> M.typ = fun t -> match t with
            | TInt -> TyInt
            | TBool -> TyBool
            | TString -> TyString
            | TPair (t1,t2) -> TyPair (trans t1, trans t2)
            | TLoc t -> TyLoc (trans t)
            (* | TFun (t1,t2) -> TyArrow (trans (SimpleTyp t1), trans (SimpleTyp t2)) *)
            | _ -> raise (M.TypeError "trans")


(* TODO : Implement this function *)
let check : M.exp -> M.typ = fun exp ->
    let alp=TVar(new_var()) in
    trans((malg [] exp alp) alp)

