
(* attributes as strings *)
type attr = string

module Attr = struct
  type t = attr
(*   let compare = Pervasives.compare *) (* 4.07  and earlier *)
  let compare = Stdlib.compare 
end

(* set of attributes, ranged over by $A,B,C$, as OCaml set of attr *)
module SetofAttr = Set.Make(Attr)

(* homogeneous set of values, ranged over by $a,b,c$ *)
type value =
    Int of int
  | Flt of float
  | Str of string
  | Bol of bool

(* comparator of value *)
let compare_value : value -> value -> int = (* Pervasives.compare *) Stdlib.compare

module MapofAttr = Map.Make(Attr)

(* Records, ranged over by $m,n,l$, partial functions from attributes to values,
  as  OCaml map from  attr to value *)
type record = value MapofAttr.t

(* Relation, ranged over by $M, N, L$, as sets of records  *)
module Record = struct
  type t = record
  let compare = MapofAttr.compare compare_value
end

module SetofRecord = Set.Make(Record)

type relation = SetofRecord.t

(* expressions for predicates  *)
type phrase =
   PCns of value (* constant *)
 | PAnd of phrase * phrase (* conjunction *)
 | POr  of phrase * phrase (* disjunction *)
 | PNot of phrase (* negation *)
 | PVar of attr (* attribute reference *)
 | PLt  of phrase * phrase (*i <  i*) (* $<$  *)
 | PGt  of phrase * phrase (*i >  i*) (* $>$  *)
 | PLte of phrase * phrase (*i <= i*) (* $\le$  *)
 | PGte of phrase * phrase (*i >= i*) (* $\ge$  *)
 | PEq  of phrase * phrase (* = *) 
 | PCase of
     ((phrase * phrase) list) (* when ... then *)
   * phrase (* else *)

(*i phrase_map i*)(* phrase\_map: apply function $f$ to every node in phrase $p$ *)
let rec phrase_map (f:phrase -> phrase) p : phrase = match p with
   PCns _ | PVar _ -> f p
 | PAnd (p1,p2) -> f (PAnd (phrase_map f p1,phrase_map f p2))
 | POr  (p1,p2) -> f (POr  (phrase_map f p1,phrase_map f p2))
 | PLt  (p1,p2) -> f (PLt  (phrase_map f p1,phrase_map f p2))
 | PGt  (p1,p2) -> f (PGt  (phrase_map f p1,phrase_map f p2))
 | PLte (p1,p2) -> f (PLte (phrase_map f p1,phrase_map f p2))
 | PGte (p1,p2) -> f (PGte (phrase_map f p1,phrase_map f p2))
 | PEq  (p1,p2) -> f (PEq  (phrase_map f p1,phrase_map f p2))
 | PNot p1 -> f (PNot (phrase_map f p1))
 | PCase (when_clause_list,else_clause) ->
     f (PCase
       (List.map (fun (p1,p2) -> (phrase_map f p1,phrase_map f p2)) when_clause_list,
	phrase_map f else_clause))

(* phrase type *)
type ptype =
    TInt (* int *)
  | TFlt (* float *)
  | TStr (* string *)
  | TBol (* bool *)

(* type environment : maps attr to ptype *)
type tenv = ptype MapofAttr.t

(* simple FD representation : pair of sets of attributes *)
type fd = SetofAttr.t * SetofAttr.t

let compare_fd (fd1:fd) (fd2:fd) : int = 
  let ((x,y),(x',y')) = (fd1,fd2) in
  let c = SetofAttr.compare x x' in
  if c = 0 
  then SetofAttr.compare y y'
  else c

(* set of fd *)
module FD = struct
  type t = fd
  let compare = compare_fd
end

module SetofFD = Set.Make(FD)

(* set of set of attributes *)
module PSetofAttr = Set.Make(SetofAttr)

(* map of nodes *)
module MapofSetofAttr = Map.Make(SetofAttr)

(* relation name *)
type rname = string

(* database instances, ranged over by $I,J$, are 
   finite maps from relation names to relations *)

module Rname = struct
  type t = rname
  let compare = (* Pervasives *)Stdlib.compare
end

module MapofRname = Map.Make(Rname)

(* sort : quadruple of domain $U$, (attribute type environment), predicate $P$ and functional dependencies $F$ *)
type sort = SetofAttr.t * tenv * phrase * SetofFD.t

(* database: map from rname to pair of sort and relation *)
type database = (sort * relation) MapofRname.t

(* change set *)
(* multiplicity mult: delete, keep, insert *)
type mult = 
    Delete  (* -1 *)
  | Keep    (*  0 *)
  | Insert  (* +1 *)

(* change entry as a pair of record (Horn's row) and multiplicity *)
type change_entry = record*mult

let compare_change_entry (ce1:change_entry) (ce2:change_entry) : int =
    let ((rec1,mul1),(rec2,mul2)) = (ce1,ce2) in
    let c = MapofAttr.compare compare_value rec1 rec2 in
    if c = 0
    then (* Pervasives *)Stdlib.compare mul1 mul2 
    else c

module ChangeEntry = struct
  type t = change_entry
  let compare = compare_change_entry
end

module SetofChange = Set.Make(ChangeEntry)

module PRecord = struct
   type t = record * record
  let compare (rec1,rec2) (rec1',rec2')  = 
    let c = MapofAttr.compare compare_value rec1 rec1' in
    if c = 0
    then MapofAttr.compare compare_value rec2 rec2' 
    else c
end

module SetofPRecord = Set.Make(PRecord)

(* pair of FD and set of pair of records *)
module FDSPRecord = struct
  type t = fd * SetofPRecord.t
  let compare (fd,s) (fd',s')  =
    let c = compare_fd fd fd' in
    if c = 0
    then SetofPRecord.compare s s'
    else c
end

(*    (fd * ((record * record) set)) set  used for update set *)
module SetofFDSPRecord = Set.Make(FDSPRecord)

(* tentative type definition for lens in the thesis *)
type ilens = sort * relation

(*p \input{macro} *)
(* $v \in \Sigma \leftrightarrow \Delta$ *)
type lens =
    Select  of rname * phrase * rname (*i select frm R where P as S i*)(* $\mt{select\ from}\ R\ \mt{where}\ P\ \mt{as}\ S$ *)
  | JoinDL  of (rname * rname)  * rname (*i join_dl R, S as T i*) (* $\mt{join\_dl}\ R,\ S\ \mt{as}\ T$ *)
  | Drop    of attr  * ((attr list) * value) * rname * rname 
        (*i drop A determined by (X,a) from R as S i*)
        (* $\mt{drop}\ A\ \mt{determined\ by}\ (X,a)\ \mt{from}\ R\ \mi{as}\ S$ *)
  | Compose of lens * lens


