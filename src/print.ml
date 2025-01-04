open Rellens_types

let pp_attr (fmt:Format.formatter) (a:attr) = Format.fprintf fmt "%s" a

(* simple printer for a sequence *)
let pp_seq (delim:string) (pp_a: Format.formatter -> 'a -> unit) (fmt:Format.formatter) 
    (xs: 'a list) : unit =
  let n = List.length xs in
  List.iteri (fun i e ->
    if i = (n - 1)  (* last element *)
    then Format.fprintf fmt "@[%a@]"   pp_a e
    else Format.fprintf fmt "@[%a%s@]@," pp_a e delim) xs

let pp_SetofAttr (fmt:Format.formatter) 
   (s: SetofAttr.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_attr) (SetofAttr.elements s)

let pp_value (fmt:Format.formatter) (v:value) = match v with 
    Int i -> Format.pp_print_int    fmt i
  | Flt f -> Format.pp_print_float  fmt f
  | Str s -> Format.fprintf fmt "%S" s
  | Bol b -> Format.pp_print_bool   fmt b

let pp_pair (pp_a: Format.formatter -> 'a -> unit) (pp_b: Format.formatter -> 'b -> unit)
            (fmt:Format.formatter) (p: 'a * 'b)  : unit
                 = Format.fprintf fmt "(%a,%a)" pp_a (fst p) pp_b (snd p)

let pp_mapsto (pp_a: Format.formatter -> 'a -> unit) (pp_b: Format.formatter -> 'b -> unit)
            (fmt:Format.formatter) (p: 'a * 'b)  : unit
                 = Format.fprintf fmt "%a -> %a" pp_a (fst p) pp_b (snd p)


let pp_MapofAttr (pp_a : Format.formatter -> 'a -> unit) (fmt:Format.formatter) 
   (m: 'a MapofAttr.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," (pp_mapsto pp_attr pp_a)) (MapofAttr.bindings m)

let pp_MapofAttr2value = pp_MapofAttr pp_value

let pp_record = pp_MapofAttr2value


let pp_SetofRecord (fmt:Format.formatter) 
   (s: SetofRecord.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_record) (SetofRecord.elements s)

let pp_relation = pp_SetofRecord

(* operator precedence *)(*i : -1 if p1 < p2, 1 if p1 > p2, 0 if p1 = p2$ i*)
(* 
 $\mathtt{op\_prec}\ p_1\ p_2 =
 \begin{cases}
   -1 & \text{if}\ p_1 < p_2 \\
    1 & \text{if}\ p_1 > p_2 \\
    0 & \text{if}\ p_1 = p_2.
  \end{cases}$
*)
let op_prec (p1:phrase) (p2:phrase) : int = 
  let forget_value (p:phrase) : phrase =
      phrase_map (fun p -> match p with
    PCns v -> PCns (Bol false)
  | PVar a -> PVar ""
  | PCase (_,_) -> PCase([],PCns (Bol false))
  | _ -> p ) p in
  if (forget_value p1 = forget_value p2) then 0 else match (p1,p2) with
    (PCns _,PVar _) -> 0 
  | (PVar _,PCns _) -> 0
  | (PCns _,_     ) -> 1
  | (PVar _,_     ) -> 1
  | (PAnd _,POr _ ) -> 1
  | (POr _ ,PAnd _ )-> -1
  | (PNot _,_     ) -> 1
  | ( _,    PNot _ )-> -1
  | (PCase _,_)      -> -1
  | (_     , PCase _)-> 1
  | _               -> 0

let rec pp_phrase (fmt:Format.formatter) (p:phrase) : unit = match p with
  PCns v -> pp_value fmt v
| PAnd (p1,p2) | POr (p1,p2) | PLt  (p1,p2) | PGt  (p1,p2) | PLte (p1,p2) 
| PGte (p1,p2) | PEq (p1,p2) ->
   (if op_prec p p1 = 1
   then Format.fprintf fmt "(%a)"  pp_phrase p1
   else  Format.fprintf fmt "%a"    pp_phrase p1);
   (match p with
    | PAnd (p1,p2) -> Format.fprintf fmt " && "
    | POr  (p1,p2) -> Format.fprintf fmt " || "
    | PLt  (p1,p2) -> Format.fprintf fmt " < "
    | PGt  (p1,p2) -> Format.fprintf fmt " > "
    | PLte (p1,p2) -> Format.fprintf fmt " <= "
    | PGte (p1,p2) -> Format.fprintf fmt " >= "
    | PEq  (p1,p2) -> Format.fprintf fmt " = "
    | _            -> failwith "pp_phrase: invalid operator");
   (if op_prec p p2 = 1
   then Format.fprintf fmt "(%a)"  pp_phrase p2
   else Format.fprintf fmt "%a"    pp_phrase p2)
| PNot p'       ->
   (if op_prec p p' = 1
   then Format.fprintf fmt "not (%a)@?"   pp_phrase p'
   else Format.fprintf fmt "not %a@?"   pp_phrase p')
| PVar a       -> pp_attr fmt a
| PCase (when_clause_list,else_clause) ->
    Format.fprintf fmt "CASE @[%a@] ELSE %a" pp_wcl when_clause_list
      pp_phrase else_clause
and pp_wcl (fmt:Format.formatter) (l:(phrase*phrase) list) :unit =
  Format.fprintf fmt "%a@," (pp_seq " " pp_wc) l
and pp_wc  (fmt:Format.formatter) ((w,t): (phrase * phrase)): unit = 
  Format.fprintf fmt "WHEN %a THEN %a@," pp_phrase w pp_phrase t

let pp_ptype (fmt:Format.formatter) (t:ptype) = match t with 
    TInt -> Format.pp_print_string fmt "int"
  | TFlt -> Format.pp_print_string fmt "float"
  | TStr -> Format.pp_print_string fmt "string"
  | TBol -> Format.pp_print_string fmt "bool"

let pp_MapofAttr2ptype = pp_MapofAttr pp_ptype

let pp_tenv = pp_MapofAttr2ptype

let pp_fd = pp_mapsto pp_SetofAttr pp_SetofAttr

let pp_SetofFD (fmt:Format.formatter) 
   (s: SetofFD.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_fd) (SetofFD.elements s)

let pp_fds = pp_SetofFD

let pp_PSetofAttr (fmt:Format.formatter) 
   (s: PSetofAttr.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_SetofAttr) (PSetofAttr.elements s)

let pp_MapofSetofAttr (pp_a : Format.formatter -> 'a -> unit) (fmt:Format.formatter) 
   (m: 'a MapofSetofAttr.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," (pp_mapsto pp_SetofAttr pp_a)) (MapofSetofAttr.bindings m)

let pp_MapofSetofAttr2PSetofAttr = pp_MapofSetofAttr pp_PSetofAttr 

let pp_rname (fmt:Format.formatter) (a:rname) = Format.fprintf fmt "%S" a

let pp_MapofRname (pp_a : Format.formatter -> 'a -> unit) (fmt:Format.formatter) 
   (m: 'a MapofRname.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," (pp_mapsto pp_rname pp_a)) (MapofRname.bindings m)

let pp_triple 
    (pp_a: Format.formatter -> 'a -> unit)
    (pp_b: Format.formatter -> 'b -> unit)
    (pp_c: Format.formatter -> 'c -> unit)
    (fmt:Format.formatter) (p: 'a * 'b * 'c)  : unit = 
  let (a,b,c) = p in
  Format.fprintf fmt "(%a,%a,%a)" pp_a a pp_b b pp_c c

let pp_quadruple
    (pp_a: Format.formatter -> 'a -> unit)
    (pp_b: Format.formatter -> 'b -> unit)
    (pp_c: Format.formatter -> 'c -> unit)
    (pp_d: Format.formatter -> 'd -> unit)
    (fmt:Format.formatter) (p: 'a * 'b * 'c * 'd)  : unit = 
  let (a,b,c,d) = p in
  Format.fprintf fmt "(%a,%a,%a,%a)" pp_a a pp_b b pp_c c pp_d d

let pp_pred = pp_phrase

let pp_sort = pp_quadruple pp_SetofAttr pp_tenv pp_pred pp_fds

let pp_MapofAttr2sort = pp_MapofAttr pp_sort

let pp_database = pp_MapofRname (pp_pair pp_sort pp_relation)

let pp_MapofRname2sort = pp_MapofRname pp_sort

let pp_mult (fmt:Format.formatter) (m:mult) = match m with 
    Delete -> Format.fprintf fmt "-1"
  | Keep   -> Format.fprintf fmt " 0"
  | Insert -> Format.fprintf fmt "+1"

let pp_change_entry = pp_pair pp_record pp_mult

let pp_SetofChange (fmt:Format.formatter) (s: SetofChange.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_change_entry) (SetofChange.elements s)

let pp_MapofRname2SetofChange = pp_MapofRname pp_SetofChange

let pp_p_record = pp_pair pp_record pp_record

let pp_SetofPRecord (fmt:Format.formatter) (s: SetofPRecord.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_p_record) (SetofPRecord.elements s)

let pp_fd_srecord = pp_pair pp_fd pp_SetofPRecord

let pp_SetofFDSPRecord (fmt:Format.formatter) (s: SetofFDSPRecord.t) : unit =
   Format.fprintf fmt "{%a}" (pp_seq "," pp_fd_srecord) (SetofFDSPRecord.elements s)

(* convert to string using pretty printer pp_a *)
let toStr (pp_a:(Format.formatter -> 'a -> unit)) (arg:'a) : string =
  Format.fprintf Format.str_formatter "%a" pp_a arg;
  Format.pp_print_flush Format.str_formatter ();
  Format.flush_str_formatter ()

