
(** This file defines a bytecode compiler and a bytecode 
    interpreter for the lambda-calculus. *)
(** External credits: source code for this program was
    copied from Leroy and Gral's development accompanying
    their paper entitled 
    "Coinductive big-step operational semantics" published
    in "Information and Computation", 2007. *)

type term = 
  | Tvar of int
  | Tint of int 
  | Tfun of term
  | Tapp of term * term

type value =
  | Vint of int
  | Vclo of term * value list  

type env = value list

type instr =
  | Ivar of int
  | Iint of int
  | Iclo of instr list 
  | Iapp
  | Iret

type mcode = instr list 

type mvalue =
  | Mint of int
  | Mclo of mcode * mvalue list 

type menv = mvalue list 

type slot =
  | Sval of mvalue
  | Sret of mcode * menv

type mstack = slot list

let rec compile k = function
  | Tvar i -> (Ivar i)::k
  | Tint n -> (Iint n)::k
  | Tfun t1 -> (Iclo (compile [Iret] t1))::k
  | Tapp (t1,t2) -> compile (compile (Iapp::k) t2) t1

let rec run e s = function
  | [] -> let (Sval v)::_ = s in v
  | i::k -> match i with
     | Ivar n -> run e (Sval(List.nth e n)::s) k
     | Iint n -> run e (Sval(Mint(n))::s) k
     | Iclo c -> run e (Sval(Mclo(c,e))::s) k
     | Iapp -> let Sval(v)::Sval(Mclo(k2,e2))::s2 = s in
               run (v::e2) (Sret(k,e)::s2) k2
     | Iret -> let (Sval(v)::Sret(k2,e2)::s2) = s in
               run e2 (Sval(v)::s2) k2 

let exec t =
  let k = compile [] t in
  let Mint n = run [] [] k in
  n

(** Remark: this source code raises warnings in Caml 
    for "non-exhaustive pattern".
    We are not concerned with such a warning since we
    prove that the evaluation of well-behaved programs 
    will always satisfy all the patterns. *)
