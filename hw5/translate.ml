(*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 *)

open K
open Sm5
module Translator = struct

  (* TODO : complete this function  *)
  let rec trans : K.program -> Sm5.command = function
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
    | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
    | K.LETV (x, e1, e2) ->
      trans e1 @ [Sm5.MALLOC; Sm5.BIND x; Sm5.PUSH (Sm5.Id x); Sm5.STORE] @
      trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.READ x -> [Sm5.GET; Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
    | K.VAR id -> [Sm5.PUSH (Sm5.Id id);Sm5.LOAD]
    | K.SUB (e1,e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
    | K.MUL (e1,e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
    | K.DIV (e1,e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
    | K.EQUAL (e1,e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
    | K.LESS (e1,e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
    | K.NOT e -> trans e @ [Sm5.NOT]
    | K.ASSIGN (id,e) -> trans e @ [Sm5.PUSH (Sm5.Id id); Sm5.STORE; Sm5.PUSH (Sm5.Id id); Sm5.LOAD]
    | K.SEQ (e1,e2) -> trans e1 @ [Sm5.POP] @ trans e2
    | K.IF (ec,e1,e2) -> trans ec @ [Sm5.JTR (trans e1,trans e2)]
    | K.WHILE (ec,eb) -> [Sm5.PUSH (Sm5.Fn ("wi",[Sm5.BIND "#while"] @ trans ec @ [Sm5.JTR(trans eb @ trans (K.CALLV("#while",K.UNIT)),trans(K.UNIT))])); Sm5.BIND "#while"] @ trans (K.CALLV ("#while",K.UNIT)) @ [Sm5.UNBIND; Sm5.POP]
    
    | K.FOR (id,ei,ef,eb) -> trans ei @ [Sm5.MALLOC; Sm5.BIND "#i"; Sm5.PUSH (Sm5.Id "#i"); Sm5.STORE] @ trans ef @ [Sm5.MALLOC; Sm5.BIND "#f"; Sm5.PUSH (Sm5.Id "#f"); Sm5.STORE; Sm5.PUSH (Sm5.Fn ("#ni",[Sm5.BIND "#for"; Sm5.PUSH (Sm5.Id "#f"); Sm5.LOAD; Sm5.PUSH(Sm5.Id "#ni"); Sm5.LOAD; Sm5.LESS; Sm5.JTR([Sm5.PUSH(Sm5.Val(Sm5.Unit))], [Sm5.PUSH (Sm5.Id "#ni"); Sm5.LOAD; Sm5.PUSH (Sm5.Id id); Sm5.STORE] @ trans eb @ [Sm5.POP; Sm5.PUSH (Sm5.Id "#for"); Sm5.PUSH (Sm5.Id "#for"); Sm5.PUSH (Sm5.Id "#ni"); Sm5.LOAD; Sm5.PUSH (Sm5.Val (Sm5.Z 1)); Sm5.ADD; Sm5.MALLOC; Sm5.CALL])])); Sm5.BIND "#for"; Sm5.PUSH (Sm5.Id "#for"); Sm5.PUSH (Sm5.Id "#for"); Sm5.PUSH (Sm5.Id "#i"); Sm5.LOAD; Sm5.MALLOC ; Sm5.CALL; Sm5.UNBIND; Sm5.POP]

    | K.LETF (f,x,e1,e2) -> [Sm5.PUSH (Sm5.Fn (x,[Sm5.BIND f] @ trans e1)); Sm5.BIND f] @ trans e2 @ [Sm5.UNBIND; Sm5.POP]
    | K.CALLV (f,arg_exp) -> [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f)] @ trans arg_exp @ [Sm5.MALLOC; Sm5.CALL]
    | K.CALLR (f,arg_var) -> [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id arg_var); Sm5.LOAD; Sm5.PUSH (Sm5.Id arg_var); Sm5.CALL]
    | K.WRITE e -> trans e @ [Sm5.MALLOC; Sm5.BIND "#buf"; Sm5.PUSH (Sm5.Id "#buf"); Sm5.STORE; Sm5.PUSH (Sm5.Id "#buf"); Sm5.LOAD; Sm5.PUSH (Sm5.Id "#buf"); Sm5.LOAD; Sm5.UNBIND; Sm5.POP; Sm5.PUT]
    
end
