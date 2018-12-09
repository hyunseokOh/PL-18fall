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
  | TVar v -> [v]

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


let rec unify env (t1,t2) = (* (TyScheme,TyScheme) -> Subst *)
    if t1=t2 then empty_subst
    else (match (t1,t2) with
        |  (SimpleTyp ty1,SimpleTyp ty2)
        |  (GenTyp (_,ty1),GenTyp (_,ty2))
        |  (SimpleTyp ty1,GenTyp (_,ty2))
        |  (GenTyp (_,ty1),SimpleTyp ty2)
        -> (match (ty1,ty2) with
    
            | (TFun(tt1,tt2),TFun(tt1',tt2'))
            | (TPair(tt1,tt2),TPair(tt1',tt2')) ->
                let s=unify env (SimpleTyp tt1,SimpleTyp tt1') in
                let s'=unify env (subst_scheme s (SimpleTyp tt2),subst_scheme s (SimpleTyp tt2')) in
                s @@ s'
            | (TLoc tt1,TLoc tt1') -> unify env (SimpleTyp tt1,SimpleTyp tt1')
            | (TVar x,tt)
            | (tt,TVar x) -> make_subst x tt
            | _ -> raise (M.TypeError "unify")
            ) 

        | _ -> raise (M.TypeError "unify")
    )

let scheme_typ scheme = match scheme with
                        | SimpleTyp t -> t
                        | GenTyp (_,t) -> t 

let rec expans e = match e with
                    | M.APP (_,_) -> true
                    | M.LET (d,e2) ->(match d with
                            | VAL (_,e1) -> (expans e1) || (expans e2)
                            | REC (_,_,e1) -> (expans e1) || (expans e2) 
                            )
                    | _ -> false

let rec malg env exp t = match exp with (*TyEnv -> Exp -> TyScheme -> Subst *)
    | M.CONST (S s) -> unify env (t,SimpleTyp TString)
    | M.CONST (N n) -> unify env (t,SimpleTyp TInt)
    | M.CONST (B b) -> unify env (t,SimpleTyp TBool)
    | M.VAR x -> 
            let tys=List.assoc x env in
            unify env (t,subst_scheme empty_subst tys)
            

    | M.FN (x,e) ->
            let b1=TVar(new_var()) in
            let b2=TVar(new_var()) in
            let s1=unify env (t,SimpleTyp (TFun(b1,b2))) in
            let env'=(x,subst_scheme s1 (SimpleTyp b1))::(subst_env s1 env) in
            let s2=malg env' e (subst_scheme s1 (SimpleTyp b2)) in
            s2 @@ s1
            
    | M.APP (e1,e2) ->
            let tt=scheme_typ t in
            let b=TVar(new_var()) in
            let s1=malg env e1 (SimpleTyp (TFun(b,tt))) in
            let env'=subst_env s1 env in
            let s2=malg env' e2 (subst_scheme s1 (SimpleTyp b)) in
            s2 @@ s1

    | M.LET (d,e2) -> (match d with
            | VAL (x,e1) ->
                    let a=TVar(new_var ()) in
                    let s=malg env e1 (SimpleTyp a) in
                    let env'=subst_env s env in
                    let gtp= if (expans exp) then subst_scheme s (SimpleTyp a)
                             else generalize env' (s a)
                    in

                    (* let gtp=generalize env' (s a) in *)

                    let env''=(x,gtp)::env' in
                    let s'=malg env'' e2 (subst_scheme s t) in
                    s' @@ s
            
            (* | REC (f,x,e1) -> *)
                    (* let a1=TVar(new_var ()) in *)
                    (* let a2=TVar(new_var ()) in *)
                    (* let s=malg env e1 (SimpleTyp a2) in *)
                    (* let env'=subst_env s env in *)
                    (* let gtp=generalize env' ( *)
(*                      *)
      )

    | M.IF (e1,e2,e3) ->
            let a=TVar(new_var ()) in
            let s=unify env (SimpleTyp a,t) in
            let env'=subst_env s env in
            let s'=malg env' e1 (SimpleTyp TBool) in
            let env''=subst_env s' env' in
            let s''=malg env'' e2 (subst_scheme s (SimpleTyp a)) in
            let env3=subst_env s'' env'' in
            let s3=malg env3 e3 (subst_scheme s'' (subst_scheme s (SimpleTyp a))) in
            s3 @@ (s'' @@ (s' @@ s))


    | M.BOP (b,e1,e2) -> (match b with
            | ADD
            | SUB -> 
                    let s=unify env (SimpleTyp TInt,t) in
                    let env'=subst_env s env in
                    let s'=malg env' e1 (SimpleTyp TInt) in
                    let env''=subst_env s' env' in
                    let s''=malg env'' e2 (SimpleTyp TInt) in
                    s'' @@ (s' @@ s)

            | AND
            | OR ->
                    let s=unify env (SimpleTyp TBool,t) in
                    let env'=subst_env s env in
                    let s'=malg env' e1 (SimpleTyp TBool) in
                    let env''=subst_env s' env' in
                    let s''=malg env'' e2 (SimpleTyp TBool) in
                    s'' @@ (s' @@ s)

            | EQ ->
                    let a1=TVar(new_var ()) in
                    let s=unify env (SimpleTyp TBool,t) in
                    let env'=subst_env s env in
                    let s'=malg env' e1 (subst_scheme s (SimpleTyp a1)) in
                    let env''=subst_env s' env' in
                    let s''=malg env'' e2 (subst_scheme s' (subst_scheme s (SimpleTyp a1))) in
                    s'' @@ (s' @@ s)

            )

    | M.READ -> unify env (SimpleTyp TInt,t)
            

    | M.WRITE e ->
            let a = TVar(new_var()) in
            let s=unify env (SimpleTyp a,t) in
            let env'=subst_env s env in
            malg env' e (subst_scheme s (SimpleTyp a))

    | M.MALLOC e ->
            let a=TVar(new_var()) in
            let s=unify env (SimpleTyp (TLoc a),t) in
            let env'=subst_env s env in
            let s'=malg env' e (subst_scheme s (SimpleTyp a)) in
            s' @@ s

    | M.ASSIGN (e1,e2) ->
            let tt=scheme_typ t in
            let s=malg env e1 (SimpleTyp (TLoc tt)) in
            let env'=subst_env s env in
            let s'=malg env' e2 (subst_scheme s t) in
            s' @@ s

    | M.BANG e ->
            let tt=scheme_typ t in
            malg env e (SimpleTyp (TLoc tt))

    | M.SEQ (e1,e2) ->
            let a=TVar(new_var ()) in
            let s=unify env (SimpleTyp a,t) in
            let env'=subst_env s env in
            let s'=malg env' e2 (subst_scheme s (SimpleTyp a)) in
            s' @@ s

    | M.PAIR (e1,e2) ->
            let a1=TVar(new_var ()) in
            let a2=TVar(new_var ()) in
            let s=unify env (SimpleTyp (TPair(a1,a2)),t) in
            let env'=subst_env s env in
            let s'=malg env' e1 (subst_scheme s (SimpleTyp a1)) in
            let env''=subst_env s' env' in
            let s''=malg env'' e2 (subst_scheme s' (subst_scheme s (SimpleTyp a2))) in
            s'' @@ (s' @@ s)

    | M.FST e ->
            let a1=TVar(new_var ()) in
            let a2=TVar(new_var ()) in

            let s=malg env e (SimpleTyp (TPair (a1,a2))) in
            let env'=subst_env s env in
            let s'=unify env' (t,subst_scheme s (SimpleTyp a1)) in
            s' @@ s
    
    | M.SND e ->
            let a1=TVar(new_var ()) in
            let a2=TVar(new_var ()) in

            let s=malg env e (SimpleTyp (TPair (a1,a2))) in
            let env'=subst_env s env in
            let s'=unify env' (t,subst_scheme s (SimpleTyp a2)) in
            s' @@ s
        

let rec trans : typ_scheme -> M.typ = fun tysch ->
    match tysch with
    | SimpleTyp t 
    | GenTyp (_,t) ->
    
     (match t with
            | TInt -> TyInt
            | TBool -> TyBool
            | TString -> TyString
            | TPair (t1,t2) -> TyPair (trans (SimpleTyp t1), trans (SimpleTyp t2))
            | TLoc t -> TyLoc (trans (SimpleTyp t))
            (* | TFun (t1,t2) -> TyArrow (trans (SimpleTyp t1), trans (SimpleTyp t2)) *)
            | _ -> raise (M.TypeError "trans")
            )


(* TODO : Implement this function *)
let check : M.exp -> M.typ = fun exp ->
    let alp=TVar(new_var()) in
    let alpsch=SimpleTyp alp in
    trans(subst_scheme (malg [] exp alpsch) alpsch)

