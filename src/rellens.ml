
(* Relational Lenses by Bohannon et al. and its incremental version by Horn *)

open Rellens_types
open Print
   
(* domain of a record $m$ *)
(*  $\mi{dom}(m)= \{ A \mid   (A \mapsto a) \in m \}$ *)
let dom (m:record) : SetofAttr.t = 
  SetofAttr.of_list (List.map fst (MapofAttr.bindings m))

(* attribute access $m(A)$ *)
let attribute (a:attr) (m: record) : value = 
  MapofAttr.find a m

(* record extension $m[A \to a]$  *)
(* $m[A \to a] = m \cup \{ A\mapsto a\}$  *)

let extend (a:attr) (v:value) (m:record) : record = 
  MapofAttr.add a v m


(* record restriction $m[X]$ *)
(* $\mt{restrict}\ X\ m = \{ A\mapsto a \mid (A \mapsto a) \in m, A \in X \}$ *)
let restrict (x:SetofAttr.t) (m:record) : record = 
   MapofAttr.filter (fun key a -> SetofAttr.mem key x) m

(* $M:U$ -- relation $M$ has domain $U$ *)
(* dynamic check *)
let of_domain (u:SetofAttr.t) (m:relation) : bool = 
   SetofRecord.for_all (fun r -> (SetofAttr.equal u (dom r))) m


(* relational projection $M[X]$ as a restriction lifted to relation *)
(* $\{m[X] \mid m \in M \}$ *)
let restrict_relation (x:SetofAttr.t) (m:relation) : relation =
   SetofRecord.fold (fun r -> SetofRecord.add (restrict x r)) m SetofRecord.empty 

(* record equivalence *)
let record_equal (m:record) (m':record) : bool =
  MapofAttr.equal (=) m m'

(* natural join $M \bowtie N$ by simple nested loop join *)
let nat_join (m:relation) (n:relation) : relation =
  if (SetofRecord.is_empty m) then SetofRecord.empty
  else
    if (SetofRecord.is_empty n) then SetofRecord.empty
    else
      let uS = dom (SetofRecord.choose m) in
      let vS = dom (SetofRecord.choose n) in
      if ((of_domain uS m) && (of_domain vS n))
      then
	let iS = SetofAttr.inter uS vS in
	SetofRecord.fold (fun rm rms ->
	  SetofRecord.union
          (let rm'  = restrict iS rm in
	  (SetofRecord.fold (fun rn rns ->
	    let rn' = restrict iS rn in
	    if record_equal rm' rn' 
	    then SetofRecord.add (MapofAttr.merge
				    (fun k a b -> match (a,b) with
				       (Some a,Some b) -> if a=b then Some a else failwith "mismatch"
				     | (Some a,None )  -> Some a
				     | (None,Some b)   -> Some b
				     | (None,None)     -> None) rm rn) rns 
	    else rns) n rms)) rms) m SetofRecord.empty 
    else SetofRecord.empty

let lookup_type (a:attr) (env:tenv) : ptype = 
   try (MapofAttr.find a env) with
     Not_found ->
       Format.fprintf Format.err_formatter "lookup_type %a not found in type env %a@." 
	 pp_attr a pp_tenv env;
       raise Not_found

let merge_tenv (tenv1:tenv) (tenv2:tenv) : tenv =
  MapofAttr.merge
     (fun k a b -> match (a,b) with
       (Some a,Some b) -> if a=b then Some a else failwith "mismatch"
     | (Some a,None )  -> Some a
     | (None,Some b)   -> Some b
     | (None,None)     -> None) tenv1 tenv2

(* trivial type inference *)
let rec qtype (env:tenv) (p:phrase) : ptype = match p with
  PCns (Int _ ) -> TInt
| PCns (Flt _ ) -> TFlt
| PCns (Str _ ) -> TStr
| PCns (Bol _ ) -> TBol
| PVar a -> lookup_type a env 
| PCase (wt_phrase_list,else_phrase) ->
    (match wt_phrase_list with
      [] -> qtype env else_phrase
    | (w,t)::wts ->
	let check_when p =
	  if qtype env p <> TBol then failwith "qtype: non-boolean WHEN in CASE" in
	check_when w;
	let tt = qtype env t in
	let rec qt accum_type l =
	  (match l with
	    [] ->
	      if accum_type = qtype env else_phrase then accum_type else
	      failwith "qtype: invalid else type in CASE"
	  | (w,t)::wts ->
	      check_when w;
              if accum_type = qtype env t then qt accum_type wts 
	      else failwith "qtype: invalid then clause in CASE") in 
	qt tt wts)
| PAnd (p1,p2) | POr (p1,p2) ->
    let t1,t2 = qtype env p1, qtype env p2 in
    (match t1,t2 with
      TBol,TBol -> TBol 
    | _         -> failwith "qtype: invalid operand type for boolean")
| PNot p1 ->
    let t1 = qtype env p1 in
    (match t1 with
      TBol -> TBol 
    | _      -> failwith "qtype: invalid operand type for boolean")
| PLt (p1,p2) | PGt(p1,p2) | PLte(p1,p2) | PGte(p1,p2) ->
    let t1,t2 = qtype env p1, qtype env p2 in
    (match t1,t2 with 
      TInt,TInt -> TBol
    | TFlt,TFlt -> TFlt
    | _         -> failwith "qtype: invalid operand type for comparison")
| PEq (p1,p2)  ->
    let t1,t2 = qtype env p1, qtype env p2 in
    if t1 = t2 then TBol else  failwith "qtype: invalid operand type for comparison"



(* $\sem{p}_r$ : interpret phrase $p$ on record $r$ *)
let rec eval (r:record) (p:phrase) : value = match p with
  PCns v -> v
| PAnd (p1,p2) ->
    let v1 = eval r p1 in
    let v2 = eval r p2 in
    (match (v1,v2) with
      (Bol b1,Bol b2) -> Bol (b1 && b2)
    | _               -> failwith "PAnd: non-boolean operand"
    )
| POr (p1,p2) ->
    let v1 = eval r p1 in
    let v2 = eval r p2 in
    (match (v1,v2) with 
      (Bol b1,Bol b2) -> Bol (b1 || b2) 
    | _               -> failwith "POr: non-boolean operand")
 | PNot p1 ->
    let v = eval r p1 in
    (match v with 
      (Bol b) -> Bol (not b)
    | _       -> failwith "PNot: non-boolean operand"
    )
 | PVar attr -> MapofAttr.find attr r
 | PLt (p1,p2) | PGt (p1,p2) | PLte (p1,p2) | PGte (p1,p2) -> 
    (let (v1,v2) = (eval r p1,eval r p2) in
     let op =
       match p with
       | PLt  _ -> (<)
       | PGt  _ -> (>)
       | PLte _ -> (<=)
       | PGte _ -> (>=) 
       | _      -> failwith "eval: unexpected operator" in
     match (v1,v2) with
       (Int i1,Int i2) -> Bol (op i1 i2)
     | _,_             -> failwith "comparison: mismatch operand")
 | PEq (p1,p2) -> 
     (let (v1,v2)=(eval r p1, eval r p2) in Bol (v1 = v2) )
 | PCase (wlist,else_phrase) -> eval_case r wlist else_phrase
 and eval_case (r:record) (wlist:(phrase * phrase) list) (else_phrase:phrase) : value =
  match wlist with
    (p1,p2)::ps ->
      let vp1 = eval r p1 in 
     (match vp1 with 
	Bol b ->
	  if b then eval r p2
	  else eval_case r ps else_phrase
      | _    -> failwith "non-boolean value in when condition")
  | []          -> eval r else_phrase

(* evaluator specific to boolean predicates *)
let eval_bool (r:record) (p:phrase) : bool =
  let v = eval r p in
  match v with Bol b -> b
  | _ -> failwith (Format.sprintf "eval_bool: non-boolean result %s" (toStr pp_value v))

(* predicates, ranged over by $P$ and $Q$

  $\top_U$ (top) : set of all records over the domain $U$

  negation of predicate : set complement

  $\neg_U M : \top_U \setminus M$ 

  $P \cap M$ : relational selection *)

(* $P\ ignores\ X$ : predicate $P$ does not refer to attributes in $X$ *)
let rec ignores (p:phrase) (x:SetofAttr.t) : bool =  match p with
  PCns v -> true
| PAnd (p1,p2) | POr (p1,p2) | PLt (p1,p2) | PGt (p1,p2) | PLte (p1,p2) | PGte (p1,p2) 
| PEq (p1,p2) -> ignores p1 x && ignores p2 x
| PNot p1 -> ignores p1 x
| PVar attr -> not (SetofAttr.mem attr x)
| PCase (wlist,else_phrase) -> 
    List.for_all (fun (w,t) -> ignores w x && ignores t x) wlist 
      && ignores else_phrase x

(* $M \models X \to Y$ : $M$ models functional dependency $X \to Y$ *)

(* list of all pairs of a list *)
let list_pairs (l: 'a list) : ('a * 'a) list =
   List.fold_right (fun e ->
    (@)  (List.map (fun e' -> (e,e')) l)) l []


(* naive test of $M \models X \to Y$

  by testing if $m[X]=m'[X] \Rightarrow m[Y]=m'[Y]$ for all $m,m' \in M$ *)
let models (m:relation) ((x,y):fd)  : bool =
  let lp = list_pairs (SetofRecord.elements m) in
  List.for_all (fun (m,m') ->
    if   record_equal (restrict x m) (restrict x m')
    then record_equal (restrict y m) (restrict y m')
    else true) lp


(* $\models$ lifted to set of fd *)

(* $M \models F = \bigwedge_{\mathit{fd}\in F} M \models \mathit{fd}$ *)

let models_fds (m:relation) (fds:SetofFD.t) : bool =
  SetofFD.for_all (models m) fds

(* functions on functional dependencies *)

(* $\mi{left}(F) = \cup\{ X \mid  X \to Y \in F\}$ *)
let left (fds:SetofFD.t) : SetofAttr.t = 
    SetofFD.fold (fun (x,y) ->
      SetofAttr.union x) fds SetofAttr.empty 

(* $\mi{right}(F) = \cup\{ Y \mid  X \to Y \in F\}$ *)
let right (fds:SetofFD.t) : SetofAttr.t = 
    SetofFD.fold (fun (x,y) ->
      SetofAttr.union y) fds SetofAttr.empty 

(*i name(F) = left(F) U right(F)  i*)
(* $\mi{names}(F) = \mi{left}(F) \cup \mi{right}(F)$ *)
let names (fds:SetofFD.t) : SetofAttr.t =
   SetofAttr.union (left fds) (right fds)

(* $\mi{outputs}(F) = \{ A \in U \mid \exists X \subseteq U . 
           A \notin X \mathbin{\text{and}} F \models X \to A\}$ *)
let outputs (fds:SetofFD.t) : SetofAttr.t = 
  SetofAttr.filter (fun attr ->
    SetofFD.exists (fun (x,y) ->
      (SetofAttr.mem attr y) && (not (SetofAttr.mem attr x))) fds) (right fds)


(* (literal) tree form *)

(* distinctness of sources and destinations of FD *)
exception Overlap_Between_Attributes (* overlap between sets of attributes *)

let merge_attrs (attrs:SetofAttr.t) (attrss:PSetofAttr.t) : PSetofAttr.t = 
  if SetofAttr.is_empty attrs then failwith "empty set of attributes"
  else 
    if (PSetofAttr.mem attrs attrss)
    then attrss 
    else 
      if PSetofAttr.for_all 
	  (fun s -> SetofAttr.is_empty (SetofAttr.inter s attrs)) attrss
      then PSetofAttr.add attrs attrss 
      else raise Overlap_Between_Attributes

exception Is_Cyclic
exception Multiple_Indegree

(* set of nodes (distinctness test) *)
let nodes (fds:SetofFD.t) : PSetofAttr.t = 
  SetofFD.fold (fun (x,y) ss ->
      (merge_attrs y (merge_attrs x ss))) fds PSetofAttr.empty 


let fwd (v:SetofAttr.t) (fds:SetofFD.t) : PSetofAttr.t =
   let edges = fds in
   SetofFD.fold (fun (x,y) ss ->
    if SetofAttr.equal v x then PSetofAttr.add y ss
    else ss) edges PSetofAttr.empty

let bwd (v:SetofAttr.t) (fds:SetofFD.t) : PSetofAttr.t =
   let edges = fds in
   SetofFD.fold (fun (x,y) ss ->
    if SetofAttr.equal v y then PSetofAttr.add x ss
    else ss) edges PSetofAttr.empty


(* tree form test: check if a set of FDs is in tree form *)
let is_tree (fds:SetofFD.t) : bool =
  let it () : bool =
    let nS : PSetofAttr.t = nodes fds in
    let _ = 
      PSetofAttr.iter (fun (v:SetofAttr.t) ->
	  if PSetofAttr.cardinal (bwd v fds) > 1 then raise Multiple_Indegree) nS in

    (*
    let n : int = PSetofAttr.cardinal nS in
    let i : int ref = ref 1 in
    let cv' : PSetofAttr.t MapofSetofAttr.t ref = ref MapofSetofAttr.empty in
    let cv  : PSetofAttr.t MapofSetofAttr.t ref = 
      ref (PSetofAttr.fold  (fun (v:SetofAttr.t) ->
      MapofSetofAttr.add (v:SetofAttr.t) (fwd v fds)) nS MapofSetofAttr.empty) in
    while (!i <= n) do (* largest possible cycle is of length n so no more than n iterations are necessary *)
      cv' := !cv;
      PSetofAttr.iter (fun v ->
	if PSetofAttr.mem v (MapofSetofAttr.find v !cv') then raise Is_Cyclic
	else 
	  cv := MapofSetofAttr.add v
	     (PSetofAttr.union 
		(MapofSetofAttr.find v !cv')
	        (PSetofAttr.fold 
		   (fun w ->
                     PSetofAttr.union (MapofSetofAttr.find w !cv'))
		   (fwd v fds) PSetofAttr.empty
		)
	     ) !cv
		      ) nS;
      i := !i + 1
    done; *)
    let is_cyclic (fds:SetofFD.t) (nS: PSetofAttr.t) : bool =
      let fwd v = fwd v fds in 
      (* finite map from left hand side of FD to the set of right hand sides of FD *)
      (* {v₁ ↦ fwd(v₁)   ,v₂  ↦ fwd(v₂) , ... , vₙ ↦ fwd(vₙ)} *)
      let initial_closure_map : PSetofAttr.t MapofSetofAttr.t = f2map_PSetofAttr fwd nS in
      (* extend the closure by the sets of attributes obtained by one time application of fwd *)
      let extend_by_fwd  (closure:PSetofAttr.t) : PSetofAttr.t =
        setmap_PSetofAttr (fun v -> PSetofAttr.add v (fwd v)) closure 
      in
      (* complete the map from the node to its irreflective transitive closure of fwd 
         by repeating one step extension of the closure |nS| times (number of nodes) 
         to the initial closure map *)
      let closure_map =
        PSetofAttr.fold (fun _ -> MapofSetofAttr.map extend_by_fwd) nS initial_closure_map in
      (* check if a node is in its closure, i.e.,
          ∨{v ∈ closure(v) | (v ↦ closure(v)) ∈ cosure_map } 

       =                 ⋁ v ∈ closure(v)
        (v ↦ closure(v)) ∈ cosure_map 
       *)
      MapofSetofAttr.exists PSetofAttr.mem closure_map in
    if is_cyclic fds nS then raise Is_Cyclic else
    true in
    try (it ()) with
      Is_Cyclic -> 
	Format.fprintf Format.err_formatter "%s@." "cyclic functional dependency";
	false
    | Overlap_Between_Attributes ->
	Format.fprintf Format.err_formatter "%s@." "overlap between sets of attributes";
	false
    | Multiple_Indegree ->
	Format.fprintf Format.err_formatter "%s@." "more than one in-degree";
	false


exception Not_in_Tree_Form

(* $leavs(F)$ : nodes that have no overlap with left parts of $F$ *)
(* $\{ Y \mid \exists X.X\to Y\in F \mathbin{\text{and}} Y \cap \mi{left}(F)=\emptyset \}$ *)
let leaves (fds:SetofFD.t) : PSetofAttr.t =
   if not (is_tree fds) then raise Not_in_Tree_Form else
   let leftS = left fds in
   SetofFD.fold (fun (x,y) ss ->
     if SetofAttr.is_empty (SetofAttr.inter leftS y) 
     then PSetofAttr.add y ss 
	 else ss) fds PSetofAttr.empty

(* $roots(F)$ : nodes that have no overlap with the right parts of $F$ *)
(* $\{ Y \mid \exists X.X\to Y\in F \mathbin{\text{and}} Y \cap \mi{right}(F)=\emptyset \}$ *)
let roots (fds:SetofFD.t) : PSetofAttr.t =
   if not (is_tree fds) then raise Not_in_Tree_Form else
   let rightS = right fds in
   SetofFD.fold (fun (x,y) ss ->
     if SetofAttr.is_empty (SetofAttr.inter rightS x) 
     then PSetofAttr.add x ss 
	 else ss) fds PSetofAttr.empty

(*i loader based on lists i*)
(*i
let t = List.fold_right (fun r ->
  let z = List.combine ["A";"B";"C"] r in
  SetofRecord.add 
    (List.fold_right (fun (k,v) ->
      MapofAttr.add k (Str v)) z MapofAttr.empty)) l_M SetofRecord.empty
i*)

(* right-biased combination of records $m$ and $n$ *)

(*i <-+- i*)
(*  $m \rbcr n$

  $m =          \{ A \to a1, B \to b1, C \to c1\}$

  $n =          \{ A \to a2, B \to b2,          D \to d1\}$

  $m \rbcr n  = \{ A \to a2, B \to b2, C \to c1,D \to d1\}$

 *)
let rbcr (m:record) (n:record) : record = 
  MapofAttr.merge (fun k a b -> match (a,b) with
  (Some a,Some b) -> Some b (* $dom(m) \cap  dom(n)$ : right bias *)
| (None,  Some b) -> Some b (*              $dom(n)$ : agree with $n$ *)
| (Some a,None )  -> Some a (* $dom(m)\setminus dom(n)$ : agree with $m$ *)
| (None,None)     -> None) m n

(* single-dependency record revision *)
(*i     X -> Y    
   m ----------> m'
         N           i*)

(*i \usepackage{chemarrow} i*)
(*i \newcommand{\sdrr}[2]{\mathrel \autorightarrow{\ensuremath{#1}}{\ensuremath{#2}}} i*)

(*i $m \autorightarrow{$X \to Y$}{$N$} m'$ i*)

(* $m \sdrr{X\to Y}{N} m'$ *)

let sdrr (m:record) ((x,y):fd) (n:relation) : record =
    if not (models n (x,y))
    then failwith (Format.sprintf "relation %s does not satisfy functional dependency %s"
		      (toStr pp_relation n) (toStr pp_fd (x,y)))
    else 
      let mX = restrict x m in
      let n' = SetofRecord.filter
	  (fun rn -> record_equal mX (restrict x rn)) n in
      let n' = restrict_relation (SetofAttr.union x y) n' in
      match (SetofRecord.cardinal n') with
        1 -> rbcr m (restrict y (SetofRecord.choose n')) (* (C-Match) *)
      | 0 -> m (* C-NoMatch *)
      | _ -> failwith (Format.sprintf
	   "multiple match %s under functional dependency %s@." 
			 (toStr pp_relation n') (toStr pp_fd (x,y)))


(*  record revision of $m$ to $n$ under set of functional dependencies $F$ *)
(*i   F
   m ====> n 
      L        i*)

(*i $m \underset{L}{\overset{F}{\Longrightarrow}} n$ i*)
(* $m \recordrevision{L}{F} n$ *)
let rec record_revision (m:record) (fds:SetofFD.t) (l:relation) : record = 
  if SetofFD.is_empty fds 
  then m (* (FC-Empty) *)
  else (* (FC-Step) *)
    if not (models_fds l fds) then failwith
      (Format.sprintf 
	   "relation %s does not satisfy functional dependencies %s@." 
	 (toStr pp_relation l)  (toStr pp_fds fds))
    else (* $L \models F,X\to Y$ *)
      if not (is_tree fds) then raise Not_in_Tree_Form 
      else (* $F,X\to Y$ is in tree form *)
	(* choose an FD with root on its left *)
	let fd = 
	  let rS = roots fds in
	  SetofFD.choose
	    (SetofFD.filter (fun (x',y') ->
	      PSetofAttr.mem x' rS) fds) in
	let _ = Format.fprintf Format.err_formatter "x->y = %a@." pp_fd fd in 
	let f  = SetofFD.remove fd fds in
	let _ = Format.fprintf Format.err_formatter "f = %a@." pp_fds f in 
	let m' = sdrr            m fd l in
     	         record_revision m' f l


(* relation revision  *)
(*i 
      M <---  L
            F          i*)
(* $M \leftarrow_F L = \{ m'\mid m \recordrevision{L}{F} m'\ \text{for some}\ m \in M\}$ *)
let relation_revision (m:relation) (fds:SetofFD.t) (l:relation) : relation = 
  SetofRecord.fold (fun m ms ->
    SetofRecord.add (record_revision m fds l) ms) m SetofRecord.empty

(* relational merge *)
(*i    U
   M <----  L
         F      i*)
(* $M \relationalmerge{F} L = M \leftarrow_F L \cup L$  *)
let relational_merge (m:relation) (fds:SetofFD.t) (l:relation) : relation = 
  SetofRecord.union (relation_revision m fds l) l



(* sort function $sort(R)$ *)
let sort (r:rname) (db:database) : sort = 
  fst (MapofRname.find r db)

(* instance $I(R)$ *)
let instance (r:rname) (db:database) : relation =
  snd (MapofRname.find r db)

(* functional dependencies of relation $R$ : $\mathit{fd}(R)$ *)
let fd (r:rname) (db:database) : SetofFD.t =
  let ((_,_,_,fds),_) = MapofRname.find r db in
  fds

(* select lens *)
(*i select from R where P as S i*)

(* 
 $\frac{
\begin{array}{c}
  \mi{sort}(R) = (U,Q,F)\\
  \mi{sort}(S) = (U,P\cap Q,F) \\
 F\ \text{is in tree form} \quad Q\ \text{ignores}\ \mi{outputs}(F)
\end{array}}
{\begin{array}{c}
\mt{select\ from}\ R\ \mt{where}\ P\ \mt{as}\ S \in\\
\Sigma \uplus \{R\} \Leftrightarrow \Sigma \uplus \{S\}
\end{array}
}\ \text{(\textsc{T-Select})}
$
*)

(* type check and inference for select *)
let typeinf_select (p:phrase) (srt:sort) : sort = 
  let (u,tenv,q,fds) = srt in
  if qtype tenv p <> TBol then failwith 
       (Format.sprintf
	 "typeinf_select: non-boolean predicate %s@." (toStr pp_phrase p)) else
   if not (is_tree fds) (* check tree form *) then raise Not_in_Tree_Form else 
   let o_fds = outputs fds in
   if not (ignores q o_fds) (* check if $Q$ ignores $outputs(F)$ *) then failwith
      (Format.sprintf "predicate %s does not ignore outputs(%s)=%s@." 
	 (toStr pp_phrase q) (toStr pp_fds fds) (toStr pp_SetofAttr o_fds)) else
     (u,tenv,PAnd (p,q),fds)

(* get part of select lens *)
(* $v\lget(I) = I\setminus_R[S\mapsto P\cap I(R)]$ *)
let get_select (r:rname) (p:phrase) (s:rname) (db:database) : database =
   let (sortR,relation) = MapofRname.find r db in
   let sortS = typeinf_select p sortR in
   let db' = MapofRname.remove r db in
   MapofRname.add s (sortS,SetofRecord.filter 
		       (fun r -> eval_bool r p)  relation) db'

(* put part of select lens *)
(* $
 \begin{array}{rcl}
            v\lput(J,I) &=& J{\setminus_S}[R\mapsto M_0 \setminus N_\#]\\
  \text{where}\quad M_0 &=& (\neg P \cap I(R))\relationalmerge{F} J(S)\\
                   N_\# &=& (P \cap M_0) \setminus J(S) \\
                      F &=& fd(R)
 \end{array}
$ *)
let put_select (r:rname) (p : phrase) (s:rname) 
    ((dbJ,dbI): (database * database)) : database  =
  let (sortR,iR)  = MapofRname.find r dbI in
  let (_,_,_,fds) = sortR in
  let iR'         = SetofRecord.filter (fun r -> eval_bool r (PNot p)) iR in
  let (_    ,jS)  = MapofRname.find s dbJ in
  let m0          = relational_merge iR' fds jS in
  let n_sharp     = SetofRecord.diff (SetofRecord.filter (fun r -> (eval_bool r p)) m0) jS in
  let dbI' = MapofRname.remove s dbJ in
   MapofRname.add r (sortR,SetofRecord.diff m0 n_sharp) dbI'


(* join of two predicates $P \bowtie Q$

  $p,q : record \to bool$

  $p \bowtie q$ is true for a record $r$ in 
         $\{rp \mid r \in U,p\ rp\} \bowtie \{rq \mid rq \in V, q\ rq\}$

  $\sem{P \bowtie Q}_r$ is true for a record $r$ in 
         $\{r \mid r \in U,\sem{P}_r\} \bowtie \{r \mid r \in V, \sem{Q}_r\}$

  Example

  $\begin{array}{lrr}
     p: &a\times b\times c&                \to bool  \\
     q: &                c&\times d\times e\to bool
    \end{array}$

   for overlapped atributes, they are equal.

   so  $p \bowtie q = \lambda r \to p\ r[U] \wedge q\ r[V]$

       $\sem{P \bowtie Q}_r = \sem{P}_r \wedge \sem{Q}_r$

 *)


(* 
 $\frac{
\begin{array}{c}
  \mi{sort}(R) = (U,P,F) \quad \mi{sort}(S) = (V,Q,G) \\
  \mi{sort}(T) = (UV,P\bowtie Q,F \cup G) \\
  G \models U \cap V \to V \\
 F\ \text{is in tree form} \quad G\ \text{is in tree form}  \\
  P\ \text{ignores}\ \mi{outputs}(F) \quad Q\ \text{ignores}\ \mi{outputs}(G)
\end{array}}
{
\begin{array}{c}
\mt{join\_dl}\ R,S\ \mt{as}\ T\ \in\ \Sigma \uplus \{R,S\} \Leftrightarrow \Sigma \uplus \{T\}
\end{array}
}\ \text{(\textsc{T-Join})}
$
*)

(* type check and inference for join *)
let typeinf_join_dl (sortR:sort) (sortS:sort) : sort =
  let ((uR,tenvR,predR,fdsR)) = sortR in
  if not (is_tree fdsR) (* check tree form *) then raise Not_in_Tree_Form else 
   let o_fdsR = outputs fdsR in
   if not (ignores predR o_fdsR) (* check if $P$ ignores $outputs(F)$ *) then failwith
      (Format.sprintf "predicate %s does not ignore outputs(%s)=%s@." 
	 (toStr pp_phrase predR) (toStr pp_fds fdsR) (toStr pp_SetofAttr o_fdsR)) else
  let ((uS,tenvS,predS,fdsS)) = sortS in
  if not (is_tree fdsS) (* check tree form *) then raise Not_in_Tree_Form else 
   let o_fdsS = outputs fdsS in
   if not (ignores predS o_fdsS) (* check if $Q$ ignores $outputs(G)$ *) then failwith
      (Format.sprintf "predicate %s does not ignore outputs(%s)=%s@." 
	 (toStr pp_phrase predS) (toStr pp_fds fdsS) (toStr pp_SetofAttr o_fdsS)) else
  let sortT = (SetofAttr.union uR uS,
               merge_tenv tenvR tenvS,
		    (*i (fun mrs ->
		      let mr = restrict uR mrs in
		      let ms = restrict uS mrs in
		      predR mr && predS ms) i*)
	            PAnd (predR,predS)
		    ,
		    SetofFD.union fdsR fdsS) in
  sortT


(* \\ get part of join lens *)
(* $v\lget(I) = I{\setminus_{R,S}}[T\mapsto I(R)\bowtie I(S)]$ *)
(* TODO: check if $G \models U \cap V \to V$ *)
let get_join_dl (r:rname) (s:rname) (t:rname) (db:database) : database =
  let (sortR,iR) = MapofRname.find r db in
  let (sortS,iS) = MapofRname.find s db in
  let sortT = typeinf_join_dl sortR sortS in
  let instanceT = nat_join iR iS in
  let db = MapofRname.remove r db in
  let db = MapofRname.remove s db in
  MapofRname.add t (sortT,instanceT) db


(* put part of join lens *)
(*$
  \begin{array}{rcl}
  v\lput(J,I)       &=& J{\setminus_T}[R\mapsto M][S\mapsto N]\\
  \text{where}\quad (U,P,F) &=& \mi{sort}(R)                  \\
                    (V,Q,G) &=& \mi{sort}(S)                  \\
                       M_0  &=& I(R)\relationalmerge{F}J(T)[U]\\
                         N  &=& I(S)\relationalmerge{G}J(T)[V]\\
                         L  &=& (M_0 \bowtie N) \setminus J(T)\\
                         M  &=& M_0 \setminus L[U]
  \end{array}
$ *)
let put_join_dl (r:rname) (s:rname) (t:rname)
    ((dbJ,dbI):(database*database)) : database =
  let (sortR,iR) = MapofRname.find r dbI in
  let (u,_,_,f) = sortR in
  let (sortS,iS) = MapofRname.find s dbI in
  let (v,_,_,g) = sortS in
  let (sortT,jT) = MapofRname.find t dbJ in
  let m0 = relational_merge iR f (restrict_relation u jT) in
  let n  = relational_merge iS g (restrict_relation v jT) in
  let l  = SetofRecord.diff (nat_join m0 n) jT in
  let m  = SetofRecord.diff m0 (restrict_relation u l) in
  let dbI' = MapofRname.remove t dbJ in
  let dbI' = MapofRname.add r (sortR,m) dbI' in
  let dbI' = MapofRname.add s (sortS,n) dbI' in
  dbI'

(*
Union lens (not part of Bohannon's relational lenses, but necessary to encode
our integration scenario) *)   

(* 
 $\frac{
\begin{array}{c}
  \mi{sort}(R) = (U,P,F) \quad \mi{sort}(S) = (V,Q,G) \\
  \mi{sort}(T) = (U,P\cup Q,F) \\
  U = V \quad F \equiv G \\
 F\ \text{is in tree form} \quad G\ \text{is in tree form} \quad \textit{(tentative)} \\
  P\ \text{ignores}\ \mi{outputs}(F) \quad Q\ \text{ignores}\ \mi{outputs}(G) \quad\textit{(tentative)}
\end{array}}
{
\begin{array}{c}
\mt{union}\ R,S\ \mt{as}\ T\ \in\ \Sigma \uplus \{R,S\} \Leftrightarrow \Sigma \uplus \{T\}
\end{array}
}\ \text{(\textsc{T-Union})}
$
*)

(* {} *)

(* type check and inference for union *)
let typeinf_union (sortR:sort) (sortS:sort) : sort =
  let ((uR,tenvR,predR,fdsR)) = sortR in
  if not (is_tree fdsR) (* check tree form *) then raise Not_in_Tree_Form else
   let o_fdsR = outputs fdsR in
   if not (ignores predR o_fdsR) (* check if $P$ ignores $outputs(F)$ *) then failwith
      (Format.sprintf "predicate %s does not ignore outputs(%s)=%s@." 
	 (toStr pp_phrase predR) (toStr pp_fds fdsR) (toStr pp_SetofAttr o_fdsR)) else
  let ((uS,tenvS,predS,fdsS)) = sortS in
  if not (is_tree fdsS) (* check tree form *) then raise Not_in_Tree_Form else 
  let o_fdsS = outputs fdsS in
  if not (ignores predS o_fdsS) (* check if $Q$ ignores $outputs(G)$ *) then failwith
      (Format.sprintf "predicate %s does not ignore outputs(%s)=%s@."
	 (toStr pp_phrase predS) (toStr pp_fds fdsS) (toStr pp_SetofAttr o_fdsS)) else
  if not (MapofAttr.equal (=) tenvR tenvS) then failwith 
      (Format.sprintf "incompatible type environments: %s %s@." (toStr pp_tenv tenvR)
	     (toStr pp_tenv tenvS)) else
  (* TODO: current check is syntactical equivalence, which is too strong  *)
  if not (SetofFD.equal fdsR fdsS) then failwith
      (Format.sprintf "incompatible FDs: %s %s@." (toStr pp_SetofFD fdsR)
	     (toStr pp_SetofFD fdsS)) else
  let sortT = (uR,
               tenvR,
	            POr (predR,predS),
		    fdsR) in
  sortT

(* get part of union lens *)

(* $v\lget(I) = I{\setminus_{R,S}}[T\mapsto I(R) \relationalmerge{F} I(S)]$ *)
(* TODO: determine necessary condition and check
   in particular, simple record union may violate FD. it should be checked 
   at run time. *)
let get_union (r:rname) (s:rname) (t:rname) (db:database) : database =
  let (sortR,iR) = MapofRname.find r db in
  let (sortS,iS) = MapofRname.find s db in
  let sortT = typeinf_union sortR sortS in
  let ((uT,tenvT,predT,fdsT)) = sortT in
  let instanceT = relational_merge iR fdsT iS in (* TODO check conflict in merge.
						  currently, S wins. (by rbcr) *)
  let db = MapofRname.remove r db in
  let db = MapofRname.remove s db in
  MapofRname.add t (sortT,instanceT) db

let put_union (r:rname) (s:rname) (t:rname)
    ((dbJ,dbI):(database*database)) : database =
  let (sortR,iR) = MapofRname.find r dbI in
  let (u,_,predR,f) = sortR in
  let (sortS,iS) = MapofRname.find s dbI in
  let (v,_,predS,g) = sortS in
  let (sortT,jT) = MapofRname.find t dbJ in
  let (v,_,_,fdsT) = sortT in
  let jT_org = relational_merge iR fdsT iS in (* TODO check conflict in merge *)
  let delT  = SetofRecord.diff jT_org jT in (* deleted records *)
  let insT  = SetofRecord.diff jT jT_org in (* inserted records *)
  let iR' = SetofRecord.diff iR delT in (* delete if match *)
  let iS' = SetofRecord.diff iS delT in (* delete if match *)
  let iR' = SetofRecord.union iR' (SetofRecord.filter (fun r -> eval_bool r predR) insT) in
  let iS' = SetofRecord.union iS' (SetofRecord.filter (fun r -> eval_bool r predS) insT) in
  let dbI' = MapofRname.remove t dbJ in
  let dbI' = MapofRname.add r (sortR,iR') dbI' in
  let dbI' = MapofRname.add s (sortS,iS') dbI' in
  dbI'


(* $\mt{change\_set}\ T\ T' =
 \{(t,-1)\mid t\in T\setminus T'\} \cup
 \{(t, 0)\mid t\in T\cap      T'\} \cup
 \{(t,+1)\mid t\in T'\setminus T\}
 $ *)
let change_set (table:relation) (table':relation) : SetofChange.t = 
 let sDelete =
  SetofRecord.fold (fun t ->
    SetofChange.add (t,Delete)) (SetofRecord.diff table table') SetofChange.empty in
 let sKeep =
  SetofRecord.fold (fun t ->
    SetofChange.add (t,Keep))   (SetofRecord.inter table table') SetofChange.empty in
 let sInsert =
  SetofRecord.fold (fun t ->
    SetofChange.add (t,Insert)) (SetofRecord.diff table' table) SetofChange.empty in
  SetofChange.union (SetofChange.union sDelete sKeep) sInsert

(* relational delta merge *)
(*i    dU
   M <----  L
         F      i*)
(* $M \relationaldeltamerge{F} \Delta N = 
  (M - \{ t \mid (t,m)\in \Delta N \wedge m = -1\}) 
          \relationalmerge{F} 
       \{ t \mid (t,m)\in \Delta N \wedge m = +1\}$  *)

let relational_delta_merge (m:relation) (fds:SetofFD.t) (n:SetofChange.t) : relation = 
  relational_merge 
    (SetofRecord.diff m
      (SetofChange.fold (fun (t,m) rs ->
		if m = Delete then SetofRecord.add t rs else rs) n SetofRecord.empty))
    fds
    (SetofChange.fold (fun (t,m) rs ->
		if m = Insert then SetofRecord.add t rs else rs) n SetofRecord.empty)


(* match on *)
(*i match on t t' X = (t[X] = t'[X]) i*)
(* $\mt{match\ on}\ t\ t'\ X = (t[X] = t'[X]) = \bigwedge\{t[A]=t'[A]\mid A\in X\}$ *)
let match_on (t:record) (t':record) (cols:SetofAttr.t) : bool =
  record_equal (restrict cols t) (restrict cols t')

(* unflatten list of phrases as conjunction *)
let rec uf_and (l:phrase list) : phrase =
    match l with
     []     -> PCns (Bol true)
    |[p]    -> p
    |p::ps  -> PAnd (p,uf_and ps)

(* unflatten list of phrases as disjunction *)
let rec uf_or (l:phrase list) : phrase =
    match l with
     []     -> PCns (Bol false)
    |[p]    -> p
    |p::ps  -> POr (p,uf_or ps) 

(* production of expression to compare all columns in $\mi{cols}$ to a record $t$ *)
(* $\qquote{\bigwedge\sem{\{\qquote{\sem{c}=\sem{t[c]}} \mid c\in \mi{cols} \} } }$ *)
let match_on_expr (t:record) (cols:SetofAttr.t) : phrase =
  let col_list = SetofAttr.elements cols in
  let phrase_list = List.map (fun c -> PEq (PVar c,PCns (attribute c t))) col_list in
  uf_and phrase_list

(* multiplicity is complement with each other : $m = -m'$ *)
let is_compl (m:mult) (m':mult) : bool = 
  (m,m')=(Insert,Delete) || (m,m')=(Delete,Insert)

(* complement rows *)
(* not sure if attributes key should always be indeed keys *)
(* $\{(t',m')\mid (t',m')\in\Delta R,t[key]=t'[key],m'=-m\}$ *)
let compl_rows ((t,m):change_entry) (dR:SetofChange.t) (key:SetofAttr.t) : SetofChange.t 
=  SetofChange.filter (fun (t',m') -> 
    match_on t t' key && is_compl m m') dR

(* $\mt{get\_fd\_updates}\ \Delta R\ (X\to Y) = 
  (X\to Y,\{(t[X],t[Y]) \mid (t,+1) \in \Delta R\}) $ *)
let get_fd_updates (dR:SetofChange.t) ((x,y):fd) : fd * SetofPRecord.t =
   ((x,y), SetofChange.fold
            (fun (t,m) ss  ->
             if m = Insert then SetofPRecord.add (restrict x t,restrict y t) ss
             else ss) dR SetofPRecord.empty)


(* $\{\mathtt{get\_fd\_updates}\ \Delta R\ f \mid f \in F \}$ *)
let get_updateset (dR:SetofChange.t) (f:SetofFD.t) : SetofFDSPRecord.t =
  SetofFD.fold (fun fd ->
    SetofFDSPRecord.add (get_fd_updates dR fd)) f SetofFDSPRecord.empty


(*i
  Thesis is not clear in the distinction of an attribute and set of attributes,
  so the code in the thesis is not directly implementable.
  The following case is not taken into account:

  right(fd) is not singleton:
  A phrase usually refers to single attribute for each reference,
  so the replacement in the phrase is necessary for each attribute.
  However, var_case_expr assumes single target phrase for replacement.
  Its caller, calc_updated_var_expr should take care of that:
  ex: under fd  {A,B,C} -> {D,E},
   replacement should take place for both D and E
  Call tree:
   delta_put_select -> query_deleted_rows -> updated_pred ->
    updated_var_expr (muti->multi map, single column target) ->
     calc_updated_var_expr (multi->multi map, with single column target) ->
      var_case_expr (multi->multi map, single colum target)
      calc_update_var_expr (multi->multi map,single column target)

   var_case_expr assumes multi->single map, instead of multi single map
  So, in calc_updated_var_expr, additional parameter attr that specify the
    target is necessary to specify replacement target.
    This information should be passed to var_case_expr.
    In turn, var_case_expr should generate then clause as
       constant referring to the specified attribute of the target row in FD
i*)
(* $\mt{var\_case\_expr}\ \mi{map}\ c\ \mi{or}\ (X\to Y) := \\
\qquote{\CASE \\
\phantom{aaa} \sem{\{\qquote{\WHEN\ \sem{\mt{match\_on\_expr}\ t\ X}\ \THEN\ \sem{t'[c]}}\mid
      (t,t') \in \mi{map} \}} \\
\quad \ELSE \sem{\mi{or}} \END
}$ *)
let var_case_expr (map : SetofPRecord.t) (attr:attr) (or_phrase:phrase) (fd:fd) : phrase =
  let where_clause_list = List.map
    (fun (t,v) -> (match_on_expr t (fst fd),PCns (attribute attr v))) 
      (SetofPRecord.elements map) in
    PCase (where_clause_list, or_phrase)

let rec calc_updated_var_expr (chl : SetofFDSPRecord.t)
    (key:SetofAttr.t) (col:SetofAttr.t) (attr:attr) (or_phrase:phrase) 
    (map: SetofPRecord.t option) : phrase = 
  let (f,changes) =
    let s = SetofFDSPRecord.filter
           (fun ((x,y),changes) -> SetofAttr.equal col y) chl in
    let _ = Format.printf "s=%a@." pp_SetofFDSPRecord s in
    match SetofFDSPRecord.cardinal s with
      1 -> SetofFDSPRecord.choose s 
    | _ -> failwith 
	  (Format.sprintf "invalid cardinality %i of s %s@." (SetofFDSPRecord.cardinal s)
	     (toStr pp_SetofFDSPRecord s)) in
  let map' = match map with 
    None -> changes 
  | Some map -> 
      let m = 
           SetofPRecord.fold (fun (k,k') ss ->
	(SetofPRecord.fold (fun (k'',v) ss' ->
	  if record_equal k' k'' then SetofPRecord.add (k,v) ss'
	  else ss') map ss)) changes SetofPRecord.empty in 
      Format.printf "m=%a@." pp_SetofPRecord m;m in
  if (* SetofAttr.equal key (fst f) *)
     SetofAttr.subset (fst f) key 
     then
    var_case_expr map' attr or_phrase f
  else
    calc_updated_var_expr chl key (fst f) 
      attr (var_case_expr map' attr or_phrase f) (Some map')

let updated_var_expr (chl: SetofFDSPRecord.t) (key:SetofAttr.t) (col:attr)
 : phrase =
  calc_updated_var_expr chl key (SetofAttr.singleton col) col (PVar col) None

(* sort: target sort of the input *)         
let updated_pred (dR:SetofChange.t) (sort:sort) (p:phrase) : phrase = 
  let (u,_,pred,fds) = sort in
  let chl = get_updateset dR fds in
  let key =
    let s = roots fds in
    match PSetofAttr.cardinal s with
      1 -> PSetofAttr.choose s 
    | _ -> let error_message = 
	  (Format.sprintf 
	     "updated_pred: > 1 cardinality of keys of functional dependency %s. Merging@." 
	     (toStr pp_PSetofAttr s)) in
           Format.fprintf Format.err_formatter "%s@." error_message;
           PSetofAttr.fold (fun s -> SetofAttr.union s) s SetofAttr.empty   in
  phrase_map (fun node ->
    match node with
      PVar n -> 
	if not (SetofAttr.mem n (right fds)) then node else updated_var_expr chl key n
    | _ -> node) p

(* $\sigma_{\qquote{
\sem{\neg P}\wedge \sem{\mt{updated\_pred}\ \Delta R\ l\ P}
}}(l)$ *)
let query_deleted_rows (dR : SetofChange.t) (r:rname) (p:phrase) (dbI:database) : relation =
  let (sortR,iR) = MapofRname.find r dbI in
  let (_,tenv,_,_) = sortR in
  if qtype tenv p <> TBol then failwith 
       (Format.sprintf "query_deleted_rows: ill-typed predicate %s@." 
	  (toStr pp_phrase p)) else
  let pred = (PAnd (PNot p,updated_pred dR sortR p)) in
  SetofRecord.filter (fun r -> eval_bool r pred) iR

(* $\Delta R\cup \{(t,-1)\mid t \in \mt{query\_deleted\_rows}\ \Delta R\ l\ P\}$ *)
let delta_put_select (r:rname) (dbI:database) (p:phrase) (dR:SetofChange.t)
    : SetofChange.t =
  SetofChange.union dR
   (SetofRecord.fold (fun t ->
     SetofChange.add (t,Delete))
        (query_deleted_rows dR r p dbI) SetofChange.empty)

(*i match_on_expr: i*)
(* Thesis ignores multiplicity of change set, but deletion should be ignored *)
(* $\qquote{\bigvee\sem{\{\mt{match\_on\_expr}\ t\ x \mid (t,m) \in \Delta R\}}}$ *)
  
let any_match_expr (dR:SetofChange.t) (x:SetofAttr.t) : phrase =
  let change_list = SetofChange.elements dR in
  let phrase_list = List.map (fun (t,m) -> match_on_expr t x)
  (*i (SetofChange.filter (fun (t,m)-> m = Insert || m = Keep) change_list) i*)
 change_list in uf_or phrase_list

(* $\sigma_{\mt{any\_match\_expr}\ \Delta R\ X}(I(R)[X \cup \{A\}])$ *)

let query_lookup_table (dR:SetofChange.t) (r:rname) (db:database)
      (x:SetofAttr.t) (a:attr) : relation =
  let (_,tenv,_,_) = sort r db in
  let pred = any_match_expr dR x in
  if qtype tenv pred <> TBol then failwith
       (Format.sprintf "query_lookup_table: ill-typed predicate %s@." 
	  (toStr pp_phrase pred)) else
     SetofRecord.filter (fun r -> eval_bool r pred)
      (restrict_relation (SetofAttr.add a x) (instance r db))

let lookup_col (t:record) (a:attr) (x:SetofAttr.t)
   (v:value) (l: SetofRecord.t) =
    let c = SetofRecord.filter (fun t' -> match_on t t' x ) l  in
    match SetofRecord.cardinal c with
    | 0  -> extend a v t
    | _  -> 
	let t' = SetofRecord.choose c in
	extend a (attribute a t') t

(* delta translation for drop *)

(*
$\kw{let} L = \mt{query\_lookup\_table}\ \Delta R\ l\ X\ A$

$\{(\mt{lookup\_col}\ t\ A\ X\ a\ L, m) \mid (t, m) \in \Delta R\}$
*)

let delta_put_drop (r:rname) (db:database) (a:attr) (x:SetofAttr.t) (v:value)
    (dR:SetofChange.t) =
  let l = query_lookup_table dR r db x a in
  SetofChange.fold (fun (t,m) ->
    SetofChange.add
      (lookup_col t a x v l,m)) dR SetofChange.empty

(* decomposition of functional dependency *)
(*i F == F' U {X -> A} i*)
(* $F = F' \cup \{X \to A\}$ *)

(* arbitrary decomposition *)
let decompose_fd (f:SetofFD.t) (a:attr) : SetofFD.t * fd =
  let rec df acc fds = match fds with 
    []          -> failwith (Format.sprintf 
			       "decompose_fd: decomposition of FDs %s w.r.t. %s failed."
			       (toStr pp_SetofFD f) (toStr pp_attr a))
  | ((x,y)::ss) -> 
      if SetofAttr.mem a y then
	let f' =
	  let y' = SetofAttr.remove a y in
	  SetofFD.union (SetofFD.of_list ss)
  	  (if SetofAttr.is_empty y' then acc else
	   SetofFD.add (x,y') acc) in
	(f',(x,SetofAttr.singleton a))
      else
	df (SetofFD.add (x,y) acc) ss in
  df SetofFD.empty (SetofFD.elements f)

(* FD split for projection lens, using attributes defining attribute a *)
let decompose_fd (f:SetofFD.t) (x':SetofAttr.t) (a:attr) : SetofFD.t * fd =
  let rec df acc fds = match fds with 
    []          -> failwith (Format.sprintf 
		    "decompose_fd: decomposition of FDs %s w.r.t. (%s,%s) failed."
		    (toStr pp_SetofFD f) (toStr pp_SetofAttr x') (toStr pp_attr a))
  | ((x,y)::ss) ->
      if SetofAttr.mem a y && SetofAttr.equal x x' then
	let f' =
	  let y' = SetofAttr.remove a y in
	  SetofFD.union (SetofFD.of_list ss)
  	  (if SetofAttr.is_empty y' then acc else
	   SetofFD.add (x,y') acc) in
	(f',(x,SetofAttr.singleton a))
      else
	df (SetofFD.add (x,y) acc) ss in
  df SetofFD.empty (SetofFD.elements f)


(* tentative conversion to conjunctive normal form (CNF) *)
(*i not not P     => P
    not (P /\ Q)  => (not P) \/ (not Q)
    not (P \/ Q)  => (not P) /\ (not Q)
    (P /\ Q) \/ R => (P \/ R) /\ (Q \/ R) i*)
(*  $\neg\neg P \Rightarrow P$ *)
(*  $\neg (P \wedge Q) \Rightarrow \neg P \vee \neg Q$ *)
(*  $\neg (P \vee   Q) \Rightarrow \neg P \wedge \neg Q$ *)
(*  $(P \wedge Q) \vee R \Rightarrow (P \vee R) \wedge (Q \vee R)$ *)
let rec cnf (p:phrase) : phrase = match p with
   PCns _ -> p
 | PAnd (p1,p2) ->
    let p1' = cnf p1 in
    let p2' = cnf p2 in
    PAnd (p1',p2')
 | POr (p1,p2) ->
    let p1' = cnf p1 in
    let pR  = cnf p2 in
    (match p1' with
      PAnd (pP,pQ) -> (* distribution *) (*i  (P /\ Q) \/ R = (P \/ R) /\ (Q \/ R) i*)
      PAnd (cnf (POr (pP,pR)),cnf (POr (pQ,pR)))
    | _ ->
	(match pR with
	  PAnd (pP,pQ) ->
	    PAnd (cnf (POr (p1',pP)),cnf (POr (p1',pQ)))
	| _ -> POr (p1',pR)))
 | PNot p1 ->
     let p1' = cnf p1 in
     (match p1' with
       PNot p1'' -> p1'' (* double negation elimination *) (*i not (not P)  => P i*)
     | PAnd (p1',p2') -> (* De Morgan *) (*i not (p1 and p2) => (not p1) or (not p2) i*)
	cnf (POr (PNot p1',PNot p2'))
     | POr  (p1',p2') -> (* De Morgan *) (*i not (p1 or p2) => (not p1) and (not p2) i*)
       PAnd (cnf (PNot p1'),cnf (PNot p2'))
     | _ -> PNot p1'
     )
 | PVar _  -> p
 | PLt _   -> p
 | PGt _   -> p
 | PLte _  -> p
 | PGte _  -> p
 | PEq  _  -> p
 | PCase _ -> p

(* projection of predicates *)
(* after turning into conjunctive normal form, 
   find a disjunction that only contains reference to A 
   and detach from the rest.

 \verb|  (A = 1) and ((B = 2) or (C = 3)) -> B=2 or  C=3, A=1 |

 \verb|   B = 2  and   A = 3  and C = 2   -> B=2 and C=2, A=3 |
 *)   

(* set of free variables appear in the given phrase p *)
let rec freevars (p:phrase) : SetofAttr.t = match p with 
  PCns v -> SetofAttr.empty
 | PNot p1 -> freevars p1
 | PVar attr -> SetofAttr.singleton attr
 | PAnd (p1,p2) | POr (p1,p2) 
 | PLt (p1,p2)  | PGt (p1,p2) | PLte (p1,p2) | PGte (p1,p2) | PEq (p1,p2) -> 
    SetofAttr.union (freevars p1) (freevars p2)
 | PCase (wlist,else_phrase) -> 
     List.fold_right (fun (w,t) ss ->
	 SetofAttr.union (freevars w)
           (SetofAttr.union (freevars t) ss)) wlist (freevars else_phrase)

(* split predicate $P:U$ into a pair $(P[U-A],P[A])$ *)
(*  used for decomposition $P= P[U-A] \bowtie P[A]$ in drop lens  *)
let split_phrase (p:phrase) (a:attr) : phrase * phrase = 
 let p = cnf p (* convert p into CNF *) in
 (* flatten as list of disjunctions *)
 let rec fl (p:phrase) : phrase list = match p with
   PAnd (p1,p2) -> fl p1 @ fl p2
 | _ -> [p] in
 let l = fl p in
 let (aps,ps) = List.partition (fun p -> SetofAttr.mem a (freevars p))  l in
  (* unflatten *)
 let (faps,fps) = (uf_and aps,uf_and ps) in
 match (SetofAttr.cardinal (freevars faps)) with 
   0 | 1 -> (fps, faps)
 | _ -> (* faps contains variables other than A *)
     failwith (Format.sprintf 
       "split_phrase: conjunctive extraction of %s part from predicate %s failed"
		 (toStr pp_attr a) (toStr pp_phrase p))

(* drop lens *)


(*i drop A determined by (X,a) from R as S i*)
(* $\mt{drop}\ A\ \mt{determined\ by}\ (X,a)\ \mt{from}\ R\ \mt{as}\ S$ *)

(* 
 $\frac{
\begin{array}{c}
  \mi{sort}(R) = (U,P,F) \\
  A \in U \quad F\equiv F'\cup \{X\to A\} \\
  \mi{sort}(S) = (U-A,P[U-A],F') \\
  P= P[U-A] \bowtie P[A] \quad \{A=a\} \in P[A]
\end{array}}
{
\begin{array}{c}
\mt{drop}\ A\ \mt{determined\ by}\ (X,a)\ \mt{from}\ R\ \mi{as}\ S \in \\
\Sigma \uplus \{R\} \Leftrightarrow \Sigma \uplus \{S\}
\end{array}}\ \text{(\textsc{T-Drop})}
$
*)

(* type check and inference for drop *)
let typeinf_drop (a:attr) ((x,v):SetofAttr.t * value) (sortR:sort) : sort = 
  let (u,tenv,p,f) = sortR in
  if not (SetofAttr.mem a u) then failwith (Format.sprintf 
   "get_drop: dropped attribute %s is not in the domain %s"
   (toStr pp_attr a) (toStr pp_SetofAttr u)) else
  let (f',(xS,aS)) = decompose_fd f x a in
  let (pRest,pA) = split_phrase p a in
  if (Bol true) <> eval (MapofAttr.singleton a v) pA then 
    failwith (Format.sprintf "value v=%s does not satisfy predicate P[%s] = %s"
		(toStr pp_value v) (toStr pp_attr a) (toStr pp_phrase pA))
  else
     (SetofAttr.remove a u,MapofAttr.remove a tenv,pRest,f')

(* get part of drop lens *)
(* $v\lget(I) = I {\setminus_R}[S\mapsto I(R)[U-A]]$ *)
let get_drop (a:attr) ((x,v):SetofAttr.t * value) (r:rname) (s:rname) (dbI:database) : database = 
  let (sortR,iR) = MapofRname.find r dbI in
  let (u,_,_,_) = sortR in
  let sortS = typeinf_drop a (x,v) sortR in
    MapofRname.add s
     (sortS,restrict_relation (SetofAttr.remove a u) iR)
      (MapofRname.remove r dbI)

(* put part of the drop lens *)
(* $
\begin{array}{rcl}
              v\lput(J,I) &=& J{\setminus_S}[R\mapsto M \leftarrow_{X\to A} I(R)]       \\
       \text{where}\quad M&=& (I(R)\bowtie J(S))\cup (N_+ \bowtie \{\{A=a\}\})\\
                       N_+&=& J(S) \setminus I(R)[U-A]                        \\
                        U &=& \mi{dom}(R)
\end{array}
   $ *)

let put_drop (a:attr) ((x,v):SetofAttr.t * value) (r:rname) (s:rname)
  ((dbJ,dbI):database*database) : database =
  let (sortR,iR) = MapofRname.find r dbI in
  let (u,_,_,_) = sortR in
  let _ = typeinf_drop a (x,v) sortR in (* for typecheck *)
  let jS = instance s dbJ in
  let nPlus = SetofRecord.diff jS (restrict_relation (SetofAttr.remove a u) iR) in
  let mR = SetofRecord.union
      (nat_join iR jS)
      (nat_join nPlus (SetofRecord.singleton (MapofAttr.singleton a v))) in
  MapofRname.add r
    (sortR,relation_revision mR (SetofFD.singleton (x,SetofAttr.singleton a)) iR)
      (MapofRname.remove s dbJ)


(* key(l) compute tentative keys from sort *)
let key (l:ilens) : SetofAttr.t = 
  let ((_,_,_,fds),_) = l in
  let s = roots fds in
   PSetofAttr.fold (fun s -> SetofAttr.union s) s SetofAttr.empty

(* dom(l) *)
let idom (l:ilens) : SetofAttr.t = 
  let ((u,_,_,_),_) = l in u

let irel (l:ilens) : relation =
  let ((_,_,_,_),r) = l in r

let is_neutral ((t,m) : change_entry) : bool = (m = Keep)

(* $m \neq 0 \wedge \exists (t',m')\in\Delta R,m'=0\wedge t[\mt{key}(l_2)]=
 t'[\mt{key}(l_2)]$ *)
let ntrl_exists_right ((t,m):change_entry) (dR:SetofChange.t) (l2:ilens) : bool =
  (not (is_neutral (t,m))) && SetofChange.exists
   (fun (t',m') -> m' = Keep && match_on t t' (key l2)) dR

(* $m \neq 0 \wedge \exists (t',m')\in\Delta R,m'=-m\wedge t[\mt{key}(l_1)]=
 t'[\mt{key}(l_1)]$ *)
let compl_exists_left ((t,m):change_entry) (dR:SetofChange.t) (l1:ilens) : bool =
  (not (is_neutral (t,m))) && SetofChange.exists
   (fun (t',m') -> is_compl m m'  && match_on t t' (key l1)) dR

(* $m \neq 0 \wedge \exists (t',m')\in\Delta R,m'=-m\wedge t[\mt{key}(l_2)]=
 t'[\mt{key}(l_2)]$ *)
let compl_exists_right ((t,m):change_entry) (dR:SetofChange.t) (l2:ilens) : bool =
  (not (is_neutral (t,m))) && SetofChange.exists
   (fun (t',m') -> is_compl m m'  && match_on t t' (key l2)) dR

(* $\mt{compl\_exists\_left}\ (t,m)\ \Delta R\ l_1 \\
\wedge \exists (t',m')\in\Delta R,m'=-m\wedge 
t[\mt{key}(l_1)]= t'[\mt{key}(l_1)] \wedge t[\mt{dom}(l_1)]\neq t'[\mt{dom}(l_1)  ]$ *)
let upd_left ((t,m):change_entry) (dR:SetofChange.t) (l1:ilens) : bool =
  compl_exists_left (t,m) dR l1 &&
   SetofChange.exists (fun (t',m') -> 
     match_on t t' (key l1) && (not (match_on t t' (idom l1)))) dR


(* $\mt{compl\_exists\_right}\ (t,m)\ \Delta R\ l_2 \\
\wedge \exists (t',m')\in\Delta R,m'=-m\wedge 
t[\mt{key}(l_2)]= t'[\mt{key}(l_2)] \wedge t[\mt{dom}(l_2)]\neq t'[\mt{dom}(l_2)]$ *)
let upd_right ((t,m):change_entry) (dR:SetofChange.t) (l2:ilens) : bool =
  compl_exists_right (t,m) dR l2 &&
   SetofChange.exists (fun (t',m') -> 
     match_on t t' (key l2) && (not (match_on t t' (idom l2)))) dR

let non_upd_left ((t,m):change_entry) (dR:SetofChange.t) (l1:ilens) : bool =
  compl_exists_left (t,m) dR l1 && (not (upd_left (t,m) dR l1))

let non_upd_right ((t,m):change_entry) (dR:SetofChange.t) (l2:ilens) : bool =
  compl_exists_right (t,m) dR l2 && (not (upd_right (t,m) dR l2))

let found_any_right ((t,m) : change_entry) (l2:ilens) : bool =
    SetofRecord.exists 
    (fun r -> eval_bool r (match_on_expr t (key l2))) (irel l2)

let found_same_right ((t,m) : change_entry) (l2:ilens) : bool =
    SetofRecord.exists
    (fun r -> eval_bool r (match_on_expr t (idom l2))) (irel l2)

let found_upd_right ((t,m) : change_entry) (l2:ilens) : bool =
    found_any_right (t,m) l2 && (not (found_same_right (t,m) l2))
  

(* $\qquote{\bigvee\sem{\{\mt{match\_on\_expr}\ t\ \mi{key}
  \mid (t,m) \in \Delta R,m=-1,
    \mt{compl\_rows}\ (t,m)\ \Delta R\ \mi{key} = \emptyset\}}}$ *)
let removed_row_expr (dR:SetofChange.t) (key:SetofAttr.t) : phrase =
  uf_or
     (SetofChange.fold
        (fun (t,m) ps ->
	  if m = Delete && SetofChange.is_empty (compl_rows (t,m) dR key)
	  then (match_on_expr t key)::ps else ps) dR [])
    
(* $ \{(t,t') \mid (t,m) \in \Delta R,
    (t',m')\in \mt{compl\_rows}\ (t,m)\ \Delta R\ \mi{key}, m=-1\}$ *)
let find_changed_rows (dR:SetofChange.t) (key:SetofAttr.t) : SetofPRecord.t =
  SetofChange.fold (fun (t,m) ss ->
    if m = Delete then
      SetofPRecord.union
      (SetofChange.fold (fun (t',m') -> (SetofPRecord.add (t,t')))
	 (compl_rows (t,m) dR key) SetofPRecord.empty) ss else ss)
         dR SetofPRecord.empty

(* 
$\qquote{\bigvee\{\sem{\mt{match\_on\_expr}\ t\ X
  \mid (X\to Y)\in \mi{fds}, t[X]=t'[X], t[Y]\neq t'[Y]\}}}$
*)
let match_changes_expr ((t,t') : record * record )(fds:SetofFD.t) : phrase = 
  uf_or
    (SetofFD.fold (fun (x,y) ss ->
      if (match_on t t' x && not (match_on t t' y)) then 
	(match_on_expr t x)::ss else ss) fds [])

(*i fwd_fds {A,B,C} {{A}->{D},{B,C}->{E,F}} = {D,E,F}  i*)

let fwd_fds (s:SetofAttr.t) (fds:SetofFD.t) : SetofAttr.t =
   let edges = fds in
   SetofFD.fold (fun (x,y) ss ->
    if SetofAttr.subset x s then SetofAttr.union y ss
    else ss) edges SetofAttr.empty

let lefts (fds:SetofFD.t) : PSetofAttr.t = 
    SetofFD.fold (fun (x,y) ->
      PSetofAttr.add x) fds PSetofAttr.empty 

let closure (fd:fd) (fds:SetofFD.t) : SetofAttr.t =
 (*i start from y in (x,y) = fd
    frontier' = fwd_fds frontier fds 
    add frontier' to the accumulated result until fixpoint is reached i*)
  let rec cl (acc:SetofAttr.t) (frontier:SetofAttr.t) : SetofAttr.t =
    let frontier' = fwd_fds frontier fds in
    if SetofAttr.subset frontier' acc then (* no more new attr *) acc else
    cl (SetofAttr.union acc frontier') frontier' in
  cl (snd fd) (snd fd)

(* $\{\mi{fd} \mid \mi{fd}\in \mi{fds}, \mi{key}\subset \mt{closure}(\mi{fd},\mi{fds})\}$ *)
let defining_fds (key:SetofAttr.t) (fds:SetofFD.t) : SetofFD.t = 
  SetofFD.fold (fun fd ss ->
    if SetofAttr.subset key (closure fd fds) 
    then SetofFD.add fd ss 
    else ss) fds SetofFD.empty

(* $\qquote{\bigvee\{ \sem{\mt{match\_on\_expr}\ chl\ \mt{left}(f) \mid 
   (\mi{chl},\mi{chr}) \in \mi{changes}\}}}$ *)
let fd_changes_expr (changes:SetofPRecord.t) (f:fd) : phrase = 
  uf_or 
    (SetofPRecord.fold (fun (chl,chr) ss ->
      (match_on_expr chl (fst f))::ss) changes [])

(* $ \qquote{\bigvee\{ \sem{\mt{fd\_changes\_expr}\ \mi{changes}\ f \mid 
   f\in \mt{defining\_fds}\ J\ F,\\
   (f,\mi{changes}) \in \mt{get\_updateset}\ \Delta R\ F\}}}
 $ *)
let changes_expr (dR:SetofChange.t) (fS:SetofFD.t) (j:SetofAttr.t) : phrase =
  uf_or
    (SetofFD.fold (fun f ss ->
      (SetofFDSPRecord.fold (fun (f',changes) ss' ->
	if 0 = compare_fd f f' then
	 (fd_changes_expr changes f)::ss'
	else ss') (get_updateset dR fS) []) @ ss) (defining_fds j fS) [])

(*$ 
\qquote{      \sem{\mt{match\_on\_expr}\ t\ J} 
  \wedge \neg \sem{\mt{removed\_row\_expr}\ \Delta R\ P_d}
  \wedge \neg \sem{\mt{changes\_expr}\ \Delta R\ F\ J}
  }
$*)
let create_query_expr (t:record) (dR:SetofChange.t) (pd:SetofAttr.t)
    (j:SetofAttr.t) (fS:SetofFD.t) : phrase =
  PAnd (match_on_expr t j,
	PAnd (PNot (removed_row_expr dR pd),
	      PNot (changes_expr dR fS j)))

let remove_entry_left ((t,m):change_entry) (dR:SetofChange.t) (l1:ilens) : bool =
  m = Delete && (not (compl_exists_left (t,m) dR l1))

(* join with colums j *) (*$\bowtie_J$ *) (*i |><| i*)
let join_with_columns (j:SetofAttr.t) (l1:ilens) (l2:ilens) : ilens =
  let ((u,tenv1,p,fds1),m) = l1 in
  let ((v,tenv2,q,fds2),n) = l2 in
  if (not (SetofAttr.subset j u)) then 
    failwith (Format.sprintf "join_with_columns: left domain %s does not contain join colum %s" (toStr pp_SetofAttr u) (toStr pp_SetofAttr j));
  if (not (SetofAttr.subset j v)) then 
    failwith (Format.sprintf "join_with_columns: right domain %s does not contain join colum %s" (toStr pp_SetofAttr v) (toStr pp_SetofAttr j));
  ((SetofAttr.union u v,
    merge_tenv tenv1 tenv2,
    PAnd (p,q),
    SetofFD.union fds1 fds2),
    SetofRecord.fold (fun rm rms ->
      SetofRecord.union
	(let rm'  = restrict j rm in
	(SetofRecord.fold (fun rn rns ->
	  let rn' = restrict j rn in
	  if record_equal rm' rn' 
	    then SetofRecord.add (MapofAttr.merge
				    (fun k a b -> match (a,b) with
				       (Some a,Some b) -> if a=b then Some a else failwith "mismatch"
				     | (Some a,None )  -> Some a
				     | (None,Some b)   -> Some b
				     | (None,None)     -> None) rm rn) rns 
	    else rns) n rms)) rms) m SetofRecord.empty)

let remove_entry_right ((t,m):change_entry) (dR:SetofChange.t) 
    (l1:ilens) (l2:ilens) (j:SetofAttr.t) (fds:SetofFD.t) : bool =
  (m = Delete) && (not (compl_exists_right (t,m) dR l2))
    && (not (ntrl_exists_right (t,m) dR l2)) 
    && (not
	  (let (_,join_l1_l2) = (join_with_columns j l1 l2)  in 
	   SetofRecord.exists
           (fun r -> eval_bool r (create_query_expr t dR (key l1) j fds )) join_l1_l2))


let join_left_row ((t,m):change_entry) (dR:SetofChange.t)
    (l1:ilens) (l2:ilens) (j:SetofAttr.t) (fds:SetofFD.t) (pd:phrase) = 
  let pi_u_t = restrict (idom l1) t in
  if is_neutral (t,m) then SetofChange.singleton (pi_u_t,Keep) 
  else
    if compl_exists_left (t,m) dR l1 then
      if upd_left (t,m) dR l1 then SetofChange.singleton (pi_u_t,m) 
      else 
	if non_upd_left (t,m) dR l1 then
	  if m = Delete then SetofChange.singleton (pi_u_t,m) 
	  else SetofChange.empty
	else 
	  SetofChange.empty
    else
      if m = Delete then
	if remove_entry_left (t,m) dR l1 then 
	  if remove_entry_right (t,m) dR l1 l2 j fds then
	    if eval_bool t pd then
	      SetofChange.singleton (pi_u_t,Delete)
	    else 
    	      SetofChange.empty
	  else
	    SetofChange.singleton (pi_u_t, Delete)
	else 
	  SetofChange.empty (* OK? *)
      else (* (m = +1) *)
	SetofChange.singleton (pi_u_t,Insert)

let join_right_row ((t,m):change_entry) (dR:SetofChange.t) 
    (l1:ilens) (l2:ilens) (j:SetofAttr.t) (fds:SetofFD.t) (qd:phrase) = 
  let pi_v_t = restrict (idom l2) t in
  if is_neutral (t,m) then SetofChange.singleton (pi_v_t,Keep)
  else
    if compl_exists_right (t,m) dR l2 then
      if ntrl_exists_right (t,m) dR l2 then SetofChange.empty 
      else
	if upd_right (t,m) dR l2 then SetofChange.singleton (pi_v_t,m)
	else
	  if non_upd_right (t,m) dR l2 then
	    if m = Delete then SetofChange.singleton (pi_v_t,Keep)
	    else SetofChange.empty
	  else SetofChange.empty (* undocumented *)
    else
      if m = Delete then
	if remove_entry_right (t,m) dR l1 l2 j fds then
	  if remove_entry_left (t,m) dR l1 then
	    if eval_bool t qd then SetofChange.singleton (pi_v_t,Delete)
	    else SetofChange.empty 
	  else SetofChange.empty 
	else SetofChange.empty (* undocumented *)
      else (* (m = Insert) *)
	if found_same_right (t,m) l2 then
	  SetofChange.singleton (pi_v_t,Keep)
	else if (not (found_any_right (t,m) l2)) then SetofChange.singleton (pi_v_t,Insert)
	else if found_upd_right (t,m) l2 then
	  let ((_,_,_,_),rel_l2) = l2 in
	  let ts = 
	    SetofRecord.filter (fun r -> eval_bool r (match_on_expr t (key l2)))
	      rel_l2 in
	  let t' = 
	    match (SetofRecord.cardinal ts) with 
	      0 -> failwith "no record found"
	    | 1 -> SetofRecord.choose ts 
	    | _ -> failwith (Format.sprintf "found_upd_right: multiple record %s found"
	               (toStr pp_relation ts)) in
	  SetofChange.of_list [(pi_v_t,Insert);(t',Delete)]
	else SetofChange.empty (* undocjmented *)

(* 
$
\begin{array}{l}
 \displaystyle\left(\bigcup_{(t,m)\in\Delta R}\mt{join\_left\_row}(t,m)\ \Delta R\ l_1\ l_2\ J\ F\ P_d,\right.\\
  \displaystyle\quad\left.\bigcup_{(t,m)\in\Delta R}\mt{join\_right\_row}(t,m)\ \Delta R\ l_1\ l_2\ J\ F\ Q_d
 \right)
\end{array} 
$ *)
let delta_put_join (l1:ilens) (l2:ilens) (j:SetofAttr.t) (pd:phrase)
    (qd:phrase) (fS:SetofFD.t) (dR:SetofChange.t) : (SetofChange.t * SetofChange.t) =
  (SetofChange.fold (fun (t,m) ->
    SetofChange.union
      (join_left_row (t,m) dR l1 l2 j fS pd)) dR SetofChange.empty,
    SetofChange.fold (fun (t,m) ->
    SetofChange.union 
      (join_right_row (t,m) dR l1 l2 j fS qd)) dR SetofChange.empty)

(* $v\nearrow \in \Sigma \to \Delta$ *)
let rec get (l:lens) (dbI:database) : database = match l with
    Select (r, p, s) -> get_select  r p s dbI
  | JoinDL ((r,s),t) -> get_join_dl r s t dbI
  | Drop (a,(attr_list,v),r,s) -> get_drop a (SetofAttr.of_list attr_list,v) r s dbI
  | Compose (l1,l2) ->
      let dbJ = get l1 dbI in
      get l2 dbJ
(* $v\searrow \in \Delta\times\Sigma\to\Sigma$ *)
and put (l:lens) ((dbJ,dbI):database * database) : database = match l with
  Select (r, p, s) ->  put_select r p s (dbJ,dbI)
| JoinDL ((r,s),t) ->  put_join_dl r s t (dbJ,dbI)
| Drop (a,(attr_list,v),r,s) -> put_drop a (SetofAttr.of_list attr_list,v) r s (dbJ,dbI)
| Compose (l1,l2) ->
    let dbK = get l1 dbI in
    put l1 (put l2 (dbJ,dbK),dbI)
and delta_put (l:lens) (dbI:database) (dR:SetofChange.t) : SetofChange.t = match l with
    Select (r, p, s) -> delta_put_select r dbI p dR
  | JoinDL ((r,s),t) -> failwith "delta_put: binary operator join does not fit here"
  | Drop (a,(attr_list,v),r,s) ->
       delta_put_drop r dbI a (SetofAttr.of_list attr_list) v dR
  | Compose (l1,l2) ->
   let dbK = get l1 dbI in
   delta_put l1 dbI (delta_put l2 dbK dR)
(* because of binary operator, functional delta should 
   return map from relation to its change set *)
and delta_put_map (l:lens) (dbI:database) (dRm:SetofChange.t MapofRname.t) : 
    SetofChange.t MapofRname.t = match l with
    Select (r, p, s) ->
    let dS = MapofRname.find s dRm in
    let dR = delta_put_select r dbI p dS in
    MapofRname.add r dR (MapofRname.remove s dRm)
  | JoinDL ((r,s),t ) ->
    let dT = MapofRname.find t dRm in
    let l1 = MapofRname.find r dbI in
    let l2 = MapofRname.find s dbI in
    let ((u,_,p,fds1),_) = l1 in
    let ((v,_,q,fds2),_) = l2 in
    let j = SetofAttr.inter u v in
    let (dR,dS) = delta_put_join l1 l2 j (PCns (Bol true)) (PCns (Bol false)) 
	(SetofFD.union fds1 fds2) dT in
    MapofRname.add r dR (MapofRname.add s dS (MapofRname.remove t dRm))
   | Drop (a,(attr_list,v),r,s) ->
       let dS = MapofRname.find s dRm in
       let dR = delta_put_drop r dbI a (SetofAttr.of_list attr_list) v dS in
       MapofRname.add r dR (MapofRname.remove s dRm)
   | Compose (l1,l2) ->
   let dbK = get l1 dbI in
   delta_put_map l1 dbI (delta_put_map l2 dbK dRm)

let select r p s = Select (r, p, s)
let join_dl (r,s) t = JoinDL ((r,s),t)
let drop a (attr_list,v) r s = Drop (a,(attr_list,v),r,s)

(* 
 $\displaystyle\frac{
  v \in \Sigma \Leftrightarrow  \Sigma' \qquad
  w \in \Sigma' \Leftrightarrow \Delta
}
{
 v;w \in \Sigma \Leftrightarrow \Delta
}\ \text{(\textsc{T-Compose})}
$
*)

let compose l1 l2 = Compose (l1,l2)

(* composition lens in infix form *)
let (&:) (l1:lens) (l2:lens) : lens = compose l1 l2

(* type inference of lens, given sort on the left *)
let rec qt_lens (l:lens) (srt: sort MapofRname.t) : sort MapofRname.t = match l with
  Select (r, p, s) ->
   let sortR = MapofRname.find r srt in
     MapofRname.add s (typeinf_select p sortR) 
       (MapofRname.remove r srt)
  | JoinDL ((r,s),t) ->
  let sortR = MapofRname.find r srt in
  let sortS = MapofRname.find s srt in
  let sortT = typeinf_join_dl sortR sortS in
  MapofRname.add t sortT (MapofRname.remove r (MapofRname.remove s srt))
  | Drop (a,(attr_list,v),r,s) ->
  let sortR = MapofRname.find r srt in
  let sortS = typeinf_drop a ((SetofAttr.of_list attr_list),v) sortR in
  MapofRname.add s sortS (MapofRname.remove r srt)
  | Compose (l1,l2) ->
      let sort1 = qt_lens l1 srt in
      qt_lens l2 sort1

(*i simple instantiation of join_template i*)
(* Simple instantiation of $\mt{join\_template}_{{\relationalmergep{F}},\Phi}$ with *)
(* $\begin{array}{rcl} {\relationalmergep{F}} &=& {\relationalmerge{F}}\\
   \Phi(U,P,F)&=& (F\ \text{is tree-form})\ \text{and}\ (P\ \text{ignores}\ \mi{outputs}(F))\end{array}$ *)
(*i todo : test pd U pd = T , clarify relational merge i*)
(* TODO : statically (at least dynamically) check $P_d \cup Q_d = \top_{UV}$ *)

let put_join_template ((r:rname),(pd:phrase)) ((s:rname),(qd:phrase)) (t:rname)  
    ((dbJ,dbI):(database*database)) : database =
  let (sortR,iR) = MapofRname.find r dbI in
  let (u,_,_,f) = sortR in
  let (sortS,iS) = MapofRname.find s dbI in
  let (v,_,_,g) = sortS in
  let (sortT,jT) = MapofRname.find t dbJ in
  let m0 = relational_merge iR f (restrict_relation u jT) in
  let n0 = relational_merge iS g (restrict_relation v jT) in
  let l  = SetofRecord.diff (nat_join m0 n0) jT in
  let ll = nat_join l (restrict_relation (SetofAttr.inter u v) jT) in
  let la = SetofRecord.diff l ll in
  let m  = 
  SetofRecord.diff
   (SetofRecord.diff m0 
    (restrict_relation u (SetofRecord.filter (fun r -> eval_bool r pd) la)))
    (restrict_relation u ll) in
  let n = 
   SetofRecord.diff n0 
    (restrict_relation v (SetofRecord.filter (fun r -> eval_bool r qd) la)) in
  let dbI' = MapofRname.remove t dbJ in
  let dbI' = MapofRname.add r (sortR,m) dbI' in
  let dbI' = MapofRname.add s (sortS,n) dbI' in
  dbI'
