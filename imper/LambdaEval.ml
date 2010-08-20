
(** A simple call-by-value evaluator for lambda-terms. *)

type term =
  | Tvar of int
  | Tint of int
  | Tfun of int * term
  | Tapp of term * term

let rec subst x v t = 
  match t with
  | Tvar y -> if x = y then v else t
  | Tint _ -> t
  | Tfun(y,b) -> Tfun(y, if x = y then b else subst x v b)
  | Tapp(t1,t2) -> Tapp(subst x v t1, subst x v t2)

let rec eval t = 
  match t with
  | Tvar y -> failwith "dandling free variables"
  | Tapp(t1,t2) -> 
      let Tfun(y,b) = eval t1 in
      eval (subst y (eval t2) b)
  | _ -> t

(** Remark: the binding [let Tfun(y,b) = eval t1 in]
    raises a warning in Caml "non-exhaustive pattern".
    We are not concerned with such a warning since we
    prove that the evaluation of well-behaved programs 
    will always satisfy the pattern [Tfun(y,b)]. *)

