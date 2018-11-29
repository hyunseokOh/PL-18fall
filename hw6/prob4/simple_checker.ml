(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton Code
 *)

open M
open Pp

type var = string

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  (* Modify, or add more if needed *)

type typ_env = (M.id * typ) list
(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
      let rec subs t' = match t' with
          | TVar x' -> if (x = x') then t else t'
          | TPair (t1, t2) -> TPair (subs t1, subs t2)
          | TLoc t'' -> TLoc (subs t'')
          | TFun (t1, t2) -> TFun (subs t1, subs t2)
          | TInt | TBool | TString -> t'
      in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
      List.map (fun (x, tyscm) -> (x, subs tyscm)) tyenv

let rec unify env (t1,t2) = 
    if t1=t2 then empty_subst
    else (match (t1,t2) with
    | (TFun(tt1,tt2),TFun(tt1',tt2'))
    | (TPair(tt1,tt2),TPair(tt1',tt2')) ->
            let s=unify env (tt1,tt1') in
            let s'=unify env (s tt2,s tt2') in
            s @@ s'
    | (TLoc tt1,TLoc tt1') -> unify env (tt1,tt1')
    | (TVar x,tt)
    | (tt,TVar x) -> make_subst x tt 
    | _ -> raise (M.TypeError "unify")
    )

let rec malg env exp t = match exp with (* (env,exp,typ) -> subst) *)
     | M.CONST (S s) -> unify env (TString,t)
     | M.CONST (N n) -> unify env (TInt,t)
     | M.CONST (B b) -> unify env (TBool,t)
     | M.VAR x -> 
             let t'=List.assoc x env in
             unify env (t,t')
     
     | M.FN (x,e) -> 
             let a1=TVar(new_var ()) in
             let a2=TVar(new_var ()) in
             let s=unify env (TFun(a1,a2),t) in
             let s'=malg ((x,s a1)::(subst_env s env)) e (s a2) in
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
                let s'=malg ((x,s a)::(subst_env s env)) e2 (s t) in
                s' @@ s

            | REC (f,x,e1) -> 
                let a1 = TVar(new_var ()) in
                let a2 = TVar(new_var ()) in
                let env'=(f,(TFun(a1,a2)))::(x,a1)::env in
                let s=malg env' e1 a2 in
                let env''= subst_env s env' in
                let s'= unify env'' (a2, s a1) in
                let s'' = malg (subst_env s' env'') e2 (s' (s t)) in
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
            | ADD
            | SUB ->
                 let s=unify env (TInt,t) in
                 let env'=subst_env s env in
                 let s'=malg env' e1 TInt in
                 let s''=malg (subst_env s' env') e2 TInt in
                 s'' @@ (s' @@ s)
            | AND
            | OR ->
                 let s=unify env (TBool,t) in
                 let env'=subst_env s env in
                 let s'=malg env' e1 TBool in
                 let s''=malg (subst_env s' env') e2 TBool in
                 s'' @@ (s' @@ s)
            | EQ -> 
                 let a1=TVar(new_var ()) in
                 let s=unify env (TBool,t) in
                 let env'=subst_env s env in
                 let s'=malg env' e1 (s a1) in
                 let s''=malg (subst_env s' env') e2 (s' (s a1)) in
                 s'' @@ (s' @@ s)
            )
     | M.READ -> unify env (TInt,t)
        
     | M.WRITE e -> 
             let a=TVar(new_var ()) in
             let s=unify env (a,t) in
             malg (subst_env s env) e (s a)
             

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
             let s=unify env (a,t) in
             let s'=malg (subst_env s env) e2 (s a) in
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
    
let rec trans : typ -> M.types = fun typs ->
    match typs with
   | TInt -> TyInt
   | TBool -> TyBool
   | TString -> TyString
   | TPair (t1,t2) -> TyPair (trans t1,trans t2)
   | TLoc t -> TyLoc (trans t)
   | TFun (t1,t2) -> TyArrow (trans t1,trans t2)
   | _ -> raise(M.TypeError "trans")


(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp -> 
    let alp=TVar (new_var()) in
    trans ((malg [] exp alp) alp)
