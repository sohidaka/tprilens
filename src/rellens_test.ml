open Rellens_types
open Print
open Rellens
open Rellens_test_util

let _ = SetofAttr.of_list ["Album";"Quantity"]

let m = MapofAttr.add "Album"    (Str "Disintegration")
       (MapofAttr.add "Quantity" (Int 6)                MapofAttr.empty)

let _ = SetofAttr.elements (dom m)

let _ = MapofAttr.bindings m

let _ = attribute "Album"    m
let _ = attribute "Quantity" m

let m' = extend "Rate" (Int 5) m
let _ = MapofAttr.bindings m'

let m'' = restrict (SetofAttr.of_list ["Album";"Quantity"]) m'
let _  = MapofAttr.bindings m''


(* Albums *)

let l_Albums : (attr * int) list =
[("Disintegration",6);
 ("Show",          3);
 ("Galore",        1);
 ("Paris",         4);
 ("Wish",          5);]

let albums = List.fold_right (fun (a,q) ts ->
  SetofRecord.add
    (let m = MapofAttr.empty in
     let m = MapofAttr.add "Album"    (Str a) m in
             MapofAttr.add "Quantity" (Int q) m)
      ts) l_Albums SetofRecord.empty

(* test if a relation has specified domain *)
let _ = of_domain (SetofAttr.of_list ["Album";"Quantity"]) albums

(* simple printing of a relation *)
let _ = List.map MapofAttr.bindings (SetofRecord.elements albums)

(* restriction (projection) of relation *)
let albums' = restrict_relation (SetofAttr.of_list ["Album"]) albums

let _ = List.map MapofAttr.bindings (SetofRecord.elements albums')

(* Tracks *)
let l_Tracks : (string * int * int * string) list =
[("Lullaby", 1989,3,"Galore");
 ("Lullaby", 1989,3,"Show");
 ("Lovesong",1989,5,"Galore");
 ("Lovesong",1989,5,"Paris");
 ("Trust",   1992,4,"Wish");
]

(* Normalization of Tracks by decomposing into Track_Date_Rate and Track_Album *)
let l_Track_Date_Rate : (string * int * int) list =
[("Lullaby", 1989,3);
 ("Lovesong",1989,5);
 ("Trust",   1992,4);
]

let l_Track_Album : (string * string) list =
[("Lullaby", "Galore");
 ("Lullaby", "Show");
 ("Lovesong","Galore");
 ("Lovesong","Paris");
 ("Trust",   "Wish");
]
    
let tracks = List.fold_right (fun (t,d,r,a) ts ->
  SetofRecord.add
      (let m = MapofAttr.add "Track"    (Str t) MapofAttr.empty in
       let m = MapofAttr.add "Date"     (Int d) m in
       let m = MapofAttr.add "Rating"   (Int r) m in
       let m = MapofAttr.add "Album"    (Str a) m in m)
      ts) l_Tracks SetofRecord.empty 

let _ = List.map MapofAttr.bindings (SetofRecord.elements tracks)

let track_date_rate = List.fold_right (fun (t,d,r) ts ->
  SetofRecord.add
      (let m = MapofAttr.add "Track"    (Str t) MapofAttr.empty in
       let m = MapofAttr.add "Date"     (Int d) m in
       let m = MapofAttr.add "Rating"   (Int r) m in m)
      ts) l_Track_Date_Rate SetofRecord.empty 

let track_album = List.fold_right (fun (t,a) ts ->
  SetofRecord.add
      (let m = MapofAttr.add "Track"    (Str t) MapofAttr.empty in
       let m = MapofAttr.add "Album"    (Str a) m in m)
      ts) l_Track_Album SetofRecord.empty 
    
(* natural join *)
let tracks1 = nat_join albums tracks

(* tracks relation by natural join of track_date_rate and track_album *)
let tracks_join = nat_join track_date_rate track_album

(* tracks relation by natural join of albums and tracks_join *)
let tracks1_join = nat_join albums tracks_join

let _ = List.map MapofAttr.bindings (SetofRecord.elements tracks1)

(* tests if a relation models given functional dependency *)

(* Albums models functional dependency { Album -> Quantity } *)
let _ = models albums (SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"])  

(* Tracks models functional dependency { Track -> Date, Rating } *)
let _ = models tracks (SetofAttr.of_list ["Track"],
		       SetofAttr.of_list ["Date";"Rating"]) 

let _ = models tracks_join (SetofAttr.of_list ["Track"],
  			    SetofAttr.of_list ["Date";"Rating"]) 

(* Tracks does not model { Track -> Album } *)
let _ = models tracks  (SetofAttr.of_list ["Track"],
          	        SetofAttr.of_list ["Album"]) 


let fds = 
     SetofFD.of_list 
        [(SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"]);
	 (SetofAttr.of_list ["Track"],SetofAttr.of_list ["Date";"Rating"])]

let fds_Album = 
     SetofFD.of_list 
        [(SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"]);]

let fds_Tracks = 
     SetofFD.of_list 
        [(SetofAttr.of_list ["Track"],SetofAttr.of_list ["Date";"Rating"]);]

let _ = SetofAttr.elements (outputs fds)

let _ = List.map SetofAttr.elements (PSetofAttr.elements (nodes fds))


let _ = fwd (SetofAttr.of_list ["Album"]) fds

let _ = bwd (SetofAttr.of_list ["Quantity"]) fds

(* test if a set of functional dependencies is in tree form *)
let _ = is_tree fds

(* {A -> BC, C -> D} *)
let fds''' = 
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B";"C"]);
	 (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"])])

let _ = is_tree fds'''

(* {A -> B, A -> C, C -> D} *)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["A"],SetofAttr.of_list ["C"]);
	 (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"])])

(* {A -> B, B -> A} *)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["B"],SetofAttr.of_list ["A"])])

(* {A -> B, B -> C, C -> A} *) (* maximum cycle size by more than two nodes *)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
	 (SetofAttr.of_list ["C"],SetofAttr.of_list ["A"])])

(* {D -> A, A -> B, B -> C, C -> A} *) (* cycle that is smaller than the maximum *)
(* then more than one in-degree is detected before cycle detection *)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["D"],SetofAttr.of_list ["A"]);
	 (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
	 (SetofAttr.of_list ["C"],SetofAttr.of_list ["A"])])

(* {A -> B, B -> C, C -> D, D-> A}*)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
	 (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"]);
	 (SetofAttr.of_list ["D"],SetofAttr.of_list ["A"]);
       ])



(*  {A -> C, B -> C} *)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["C"]);
	 (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])])

(*  {A -> B, BC -> D *)
let _ = is_tree
     (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["B";"C"],SetofAttr.of_list ["D"])])

(* self cycle *)
let fds' = 
     (SetofFD.of_list
        [(SetofAttr.of_list ["Album"],SetofAttr.of_list ["Album"])])
let _ = is_tree fds'


let _ = leaves fds

let _ = roots fds

let _ = try (roots (SetofFD.of_list
        [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	 (SetofAttr.of_list ["B";"C"],SetofAttr.of_list ["D"])]); ()) with
  Not_in_Tree_Form -> Format.printf "not in tree form" 

(* relations *)
let l_M : (string * string * string) list =
   [("a1","b2","c1");
    ("a2","b1","c1");
    ("a3","b3","c3")]

let l_L : (string * string * string) list =
   [("a2","b2","c2");
    ("a4","b4","c4")]

let rM = List.fold_right (fun (a,b,c) ts ->
  SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
               MapofAttr.add "C" (Str c) m)
      ts) l_M SetofRecord.empty 

let rL = List.fold_right (fun (a,b,c) ts ->
  SetofRecord.add
      (let m = MapofAttr.empty             in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
               MapofAttr.add "C" (Str c) m
             )
      ts) l_L SetofRecord.empty 

(* right-biast combination of records *)
let _ = 
  let m = MapofAttr.empty in
  let m = MapofAttr.add "A" (Str "a1") m in
  let m = MapofAttr.add "B" (Str "b1") m in
  let m = MapofAttr.add "C" (Str "c1") m in
  let n = MapofAttr.empty in
  let n = MapofAttr.add "A" (Str "a2") n in
  let n = MapofAttr.add "B" (Str "b2") n in
  let n = MapofAttr.add "D" (Str "d2") n in
  rbcr m n

(* single dependency record revision *)
let _ = 
  let m = MapofAttr.empty in
  let m = MapofAttr.add "A" (Str "a1") m in
  let m = MapofAttr.add "B" (Str "b1") m in
  let m = MapofAttr.add "C" (Str "c1") m in
  let fd = (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]) in
  sdrr m fd rL

(* record revision *)      
let _ = 
  let m = MapofAttr.empty in
  let m = MapofAttr.add "A" (Str "a1") m in
  let m = MapofAttr.add "B" (Str "b1") m in
  let m = MapofAttr.add "C" (Str "c1") m in
  let fds = SetofFD.of_list
       [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	(SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])] in
  record_revision m fds rL

(* relation revision *)
let _ = 
  let fds = SetofFD.of_list
      [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
       (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])] in
  relation_revision rM fds rL

(* relational merge *)
let _ = 
  let fds = SetofFD.of_list
      [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
       (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])] in
  relational_merge rM fds rL

(* database of Albums and Tracks in Figure 1 of Bohannon et al. *)
let db =
  let m = MapofRname.empty in
  let sort_albums = (SetofAttr.of_list ["Album";"Quantity"],
		     mapofAttr_of_list [("Album",TStr);("Quantity",TInt)],
		     PCns (Bol true),
		     SetofFD.singleton 
		       (SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"])) in
  let sort_tracks = (SetofAttr.of_list ["Track";"Date";"Rating";"Album"],
		     mapofAttr_of_list [("Track",TStr);("Date",TInt);("Rating",TInt);
					("Album",TStr)],
		      PCns (Bol true),
		     SetofFD.singleton
                      (SetofAttr.of_list ["Track"],SetofAttr.of_list ["Date";"Rating"])) in
  let m = MapofRname.add "Albums" (sort_albums,albums) m in
  let m = MapofRname.add "Tracks" (sort_tracks,tracks) m in 
  m

(* normalized database for Figure 1 of Bohannon et al.*)
let db_norm =
  let m = MapofRname.empty in
  let sort_albums = (SetofAttr.of_list ["Album";"Quantity"],
		     mapofAttr_of_list [("Album",TStr);("Quantity",TInt)],
		     PCns (Bol true),
		     SetofFD.singleton 
		       (SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"])) in
  let sort_track_date_rate = (SetofAttr.of_list ["Track";"Date";"Rating"],
		     mapofAttr_of_list [("Track",TStr);("Date",TInt);("Rating",TInt);],
		      PCns (Bol true),
		     SetofFD.singleton
                      (SetofAttr.of_list ["Track"],SetofAttr.of_list ["Date";"Rating"])) in
  let sort_track_album = (SetofAttr.of_list ["Track";"Album"],
		     mapofAttr_of_list [("Track",TStr);("Album",TStr)],
		      PCns (Bol true),
		     SetofFD.empty) in
  let m = MapofRname.add "Albums" (sort_albums,albums) m in
  let m = MapofRname.add "Track_Date_Rate" (sort_track_date_rate,track_date_rate) m in
  let m = MapofRname.add "Track_Album" (sort_track_album,track_album) m in 
  m
    


(* select lens *)
let db_Albums' = get_select "Albums"
      (PGt (PVar "Quantity", PCns (Int 2))) "Albums'" db

let dbI =
  let m = MapofRname.empty in
  let (sort_R,relation_R) = load_string_string_string
      ["A";"B";"C"] [(["A"],["B"])]
    [("a1","b1","c1");
     ("a1","b1","c2");
     ("a2","b2","c2")] in
  let m = MapofRname.add "R" (sort_R,relation_R) m in 
  m

(* select from R where C = c2 as S *)
let dbJ = get_select "R"
       (PEq (PVar "C",PCns (Str "c2"))) "S" dbI


let dbJ' = 
  let m = MapofRname.empty in
  let sort_S = (SetofAttr.of_list ["A";"B";"C"],
		mapofAttr_of_list [("A",TStr);("B",TStr);("C",TStr)],
		     (PEq (PVar "C",PCns (Str "c2"))),
		     SetofFD.singleton 
		       (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"])) in
  let l_S : (string * string * string) list =
    [("a1","b2","c2");
     ("a2","b2","c2")] in
  let relation_S = List.fold_right (fun (a,b,c) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
               MapofAttr.add "C" (Str c) m)
      ts) l_S SetofRecord.empty in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m

let dbI' = put_select "R" 
    (PEq (PVar "C",PCns (Str "c2"))) "S"
    (dbJ',dbI)

(* sort(R) = (U,true, {A}->{B}) *)
let dbI =
  let m = MapofRname.empty in
  let (sort_R,relation_R) =
    load_string_string_string ["A";"B";"C"] [(["A"],["B"])]
    [("a1","b1","c1");] in
  let m = MapofRname.add "R" (sort_R,relation_R) m in 
  m

let dbJ = get_select "R"
      (PEq (PVar "B",PCns (Str "b2"))) "S" dbI

let dbJ' = 
  let m = MapofRname.empty in
  let sort_S = (SetofAttr.of_list ["A";"B";"C"],
		mapofAttr_of_list [("A",TStr);("B",TStr);("C",TStr)],
		(PEq (PVar "B", PCns(Str "b2"))),
		SetofFD.singleton 
		  (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"])) in
  let l_S : (string * string * string) list =
    [("a1","b2","c2");
     ] in
  let relation_S = List.fold_right (fun (a,b,c) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
               MapofAttr.add "C" (Str c) m)
      ts) l_S SetofRecord.empty in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m

let dbI' = put_select "R"
    (PEq (PVar "B", PCns (Str "b2"))) "S"
    (dbJ',dbI)

(* join_dl lens *)

let dbI =
  let m = MapofRname.empty in
  let (sort_R,relation_R) = load_string_string_string
     ["A";"B";"C"] [(["A"],["B"])] 
    [("a1","b1","c1");
     ("a2","b2","c2");
     ("a2","b2","c3");
   ] in
  let m = MapofRname.add "R" (sort_R,relation_R) m in 
  let (sort_S,relation_S) = load_string 
      ["C"]  []  
      ["c1"; 
       "c2";] in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m

(* join_dl "R","S" as T *)
let dbJ = get_join_dl "R" "S" "T" dbI

let dbJ' = 
  let (sortT,instanceT) = MapofRname.find "T" dbJ in
  let l_T : (string*string*string) list =
    [("a2","b2'","c2");
   ] in
  let relationT = List.fold_right (fun (a,b,c) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
       let m = MapofAttr.add "C" (Str c) m in
       m
      )
      ts) l_T SetofRecord.empty in
  let m = MapofRname.add "T" (sortT,relationT) dbJ in 
  m
  

let dbI' =  put_join_dl "R" "S" "T" (dbJ',dbI)

let deltaT =
 let  relation_T  = instance "T" dbJ  in
 let  relation_T' = instance "T" dbJ' in
 change_set relation_T relation_T'

let mChange = 
  let l1 = MapofRname.find "R" dbI in
  let l2 = MapofRname.find "S" dbI in
  let ((u,_,p,fds1),_) = l1 in
  let ((v,_,q,fds2),_) = l2 in
  let j = SetofAttr.inter u v in
  let (dR,dS) = delta_put_join l1 l2 j (PCns (Bol true)) (PCns (Bol false)) 
	(SetofFD.union fds1 fds2) deltaT in
    MapofRname.add "R" dR (MapofRname.singleton "S" dS)

let deltaR = MapofRname.find "R" mChange
let deltaS = MapofRname.find "S" mChange

(* In general, results may not agree between state-based and incremental 
  lens because
   Horn et al. assumes 
    there is a key on the left table that fully determines their records,
    join columns will fully determine the records on the right records *)

(* Figure 3.1 *)
let dT = 
  let l_T : (int * int * int * int) list =
    [(2,1,1,5);
     (3,2,2,6);
   ] in
  let relation_T = List.fold_right (fun (a,b,c,d) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Int a) m in
       let m = MapofAttr.add "B" (Int b) m in
       let m = MapofAttr.add "C" (Int c) m in
       let m = MapofAttr.add "D" (Int d) m in
      m)
      ts) l_T SetofRecord.empty in
  let l_T' : (int * int * int * int) list =
    [(2,1,1,5);
     (3,2,6,6);
   ] in
  let relation_T' = List.fold_right (fun (a,b,c,d) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Int a) m in
       let m = MapofAttr.add "B" (Int b) m in
       let m = MapofAttr.add "C" (Int c) m in
       let m = MapofAttr.add "D" (Int d) m in
       m) 
  ts) l_T' SetofRecord.empty in
  change_set relation_T relation_T'

(* Example (3.6) *)
let dR =
  let l_T : (int * int * int) list =
    [(1,2,3);
     (2,1,3);
     (3,4,5);
     (5,6,7);
   ] in
  let relation_T = List.fold_right (fun (a,b,c) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Int a) m in
       let m = MapofAttr.add "B" (Int b) m in
       let m = MapofAttr.add "C" (Int c) m in
      m)
      ts) l_T SetofRecord.empty in
  let l_T' : (int * int * int) list =
    [(1,3,2);
     (2,1,4);
     (3,4,5);
     (4,5,6);
   ] in
  let relation_T' = List.fold_right (fun (a,b,c) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Int a) m in
       let m = MapofAttr.add "B" (Int b) m in
       let m = MapofAttr.add "C" (Int c) m in
       m) 
  ts) l_T' SetofRecord.empty in
  change_set relation_T relation_T'

(* needed updates given changes and functional *)
let fdu = get_fd_updates dR (SetofAttr.of_list ["A";"B"],
                           SetofAttr.of_list ["C"])

let fdu = get_fd_updates dR (SetofAttr.of_list ["B"],
                           SetofAttr.of_list ["C"])

(* expression updating specified attribute *)
let vce = 
  let (f,map) = fdu in
  var_case_expr map "C" (PVar "C") f

let fds = SetofFD.of_list
       [(SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
	(SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])] 

(* update sets for given set of functional depdendencies *)
let dR_updateset = get_updateset dR fds 

(* selection after join  *)
let dbI =
  let m = MapofRname.empty in
  let (sort_R,relation_R) = load_int_int
      ["A";"B"] [(["A"],["B"])] 
    [(2,1);
     (3,2);
     (4,2);
   ] in
  let m = MapofRname.add "R" (sort_R,relation_R) m in 
  let (sort_S,relation_S) = load_int_int_int
      ["B";"C";"D"] [] 
      [(1,1,5);
       (2,2,6);
       (3,2,7);
     ] in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m

let dbJ = get_join_dl "R" "S" "T" dbI

let predJ = (POr (PGt (PVar "C",PCns (Int 3)),PLte (PVar "A",PCns (Int 3))))
let dbK = get_select "T" predJ "U" dbJ

(* predicate with specified variable reference updated according to fd *)
let up_dR = updated_pred dR (SetofAttr.of_list ["A";"B";"C"],
			     mapofAttr_of_list [("A",TInt);
					        ("B",TInt);
					        ("C",TInt);],predJ,fds) predJ

let _ = match_on_expr
   (let m = MapofAttr.empty in
    let m = MapofAttr.add "A" (Int 1) m in
    let m = MapofAttr.add "B" (Int 2) m in
    let m = MapofAttr.add "C" (Int 3) m in
    m)
    (SetofAttr.of_list ["A";"B";"C"])


(************* state based get, operation based put for SELECT *************)

(* sort(R) = (U,true, {A}->{B}) *)
let dbI =
  let m = MapofRname.empty in
  let (sort_R,relation_R) = load_string_string_string
      ["A";"B";"C"] [(["A"],["B"])]
    [("a1","b1","c1");] in
  let m = MapofRname.add "R" (sort_R,relation_R) m in 
  m

let dbJ = get_select "R"
      (PEq (PVar "B",PCns (Str "b2"))) "S" dbI

let dbJ' = 
  let m = MapofRname.empty in
  let sort_S = (SetofAttr.of_list ["A";"B";"C"],
		mapofAttr_of_list [("A",TStr);
				   ("B",TStr);
				   ("C",TStr);],
		     (PEq (PVar "B", PCns(Str "b2"))),
		     SetofFD.singleton 
		       (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"])) in
  let l_S : (string * string * string) list =
    [("a1","b2","c2");
     ] in
  let relation_S = List.fold_right (fun (a,b,c) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
               MapofAttr.add "C" (Str c) m)
      ts) l_S SetofRecord.empty in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m
(* generate change set *)
let deltaS =
 let  relation_s  = instance "S" dbJ  in
 let  relation_s' = instance "S" dbJ' in
 change_set relation_s relation_s'

(* set of deleted rows for given set of changes *)
let dr = query_deleted_rows deltaS "R" (PEq (PVar "B",PCns (Str "b2"))) dbI


(* put by incremental lens *)
let relationR' =
  let relation_r = instance "R" dbI in
  let (u,tenv,p,fds)  = sort     "R" dbI in
  let pred = (PEq (PVar "B",PCns (Str "b2"))) in
  let deltaR = 
    delta_put_select "R" dbI  pred  deltaS in
  relational_delta_merge relation_r fds deltaR

(* put by state based lens *)
let dbI' = put_select "R"
    (PEq (PVar "B",PCns (Str "b2"))) "S"
    (dbJ',dbI)

(* two results agree *)
let _ =  SetofRecord.equal relationR' (instance "R" dbI')

(* decomposition of functional dependencies into A part ant the rest,
   necessary for projection lens *)
let _ = 
   let f = SetofFD.empty in
   let f = SetofFD.add (SetofAttr.of_list ["A"], SetofAttr.of_list ["C"]) f in
   let f = SetofFD.add (SetofAttr.of_list ["B"], SetofAttr.of_list ["C"]) f in
   decompose_fd f (SetofAttr.of_list ["B"]) "C"

(* decomposition of a predicate into A part and the rest, necessary for
   projection lenses *)
(* B = 1 && A = 1 && C = 3 => (B = 1 && C = 3, A = 1) *)
let _ = split_phrase (PAnd (PEq (PVar "B",PCns (Int 1)),(PAnd ((PEq (PVar "A",PCns (Int 1))),(PEq (PVar "C",PCns (Int 3))))))) "A"

let _ = split_phrase (PAnd (PEq (PVar "B",PCns (Int 1)),(PAnd ((PEq (PVar "A",PCns (Int 1))),(PEq (PVar "C",PCns (Int 3))))))) "D"

let _ = try (split_phrase (POr (PEq (PVar "B",PCns (Int 1)),(POr ((PEq (PVar "A",PCns (Int 1))),(PEq (PVar "C",PCns (Int 3))))))) "A" ; ()) with
     Failure s -> Format.printf "Failure: %s@." s


let _ = try (split_phrase (POr (PEq (PVar "A",PCns (Int 7)),PAnd (PEq (PVar "A",PCns (Int 1)),PEq (PVar "B",PCns (Int 5))))) "A" ; ()) with
  Failure s -> Format.printf "Failure: %s@." s

(* attribute by attribute projection is more difficult compared with 
   projection by set of attributes in terms of predicate split.
   if projected attributes are {A,B} and predicate has been applied 
   for both of the attributes, then decomposition of the predicate 
   is impossible if two attributes depend each other. *)

(************* state based get, operation based put for DROP *************)

(* sort(S) = ({B,C,D},true, {B}->{C}, {B}->{D}) *)
let dbI =
  let m = MapofRname.empty in
  let (sort_S,relation_S) = load_int_int_int ["B";"C";"D"]
      [(["B"],["D"]);
       (["B"],["C"])]
    [(1,1,5);
     (2,2,6);
     (3,2,7)] in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m

(* state based get *)
let dbJ = get_drop "D" (SetofAttr.of_list ["B"],Int 4) "S" "T" dbI

let dbJ' =
  let m = MapofRname.empty in
  let (sort_T,relation_T) = load_int_int ["B";"C"]
             [(["B"],["C"])]
    [(1,1);
     (2,2);
     (4,3)] in
  let m = MapofRname.add "T" (sort_T,relation_T) m in 
  m

(* state based put *)
let dbI' = put_drop "D" (SetofAttr.of_list ["B"],Int 4) "S" "T" (dbJ',dbI)

let dT = 
    let relation_T  = instance "T" dbJ  in
    let relation_T' = instance "T" dbJ' in 
    change_set relation_T relation_T'

let any_match_phrase = any_match_expr dT (SetofAttr.of_list ["B"])


(* put by incremental lens *)
 let deltaS = delta_put_drop "S" dbI "D" (SetofAttr.of_list ["B"]) (Int 4) dT
					  
let relationS' =
  let ((_,_,_,fds),relationS) = MapofRname.find "S" dbI in
  relational_delta_merge relationS fds deltaS

(* two results agree *)
let _ =  SetofRecord.equal relationS' (instance "S" dbI')


(* test for FD with multiple target attributes *)
(* sort(S) = ({B,C,D},true, {B}->{C,D}) *)
let dbI =
  let m = MapofRname.empty in
  let (sort_S,relation_S) = load_int_int_int
   ["B";"C";"D"] [(["B"],["C";"D"])]
    [(1,1,5);
     (2,2,6);
     (3,2,7)] in
  let m = MapofRname.add "S" (sort_S,relation_S) m in 
  m

(* state based get *)
let dbJ = get_drop "D" (SetofAttr.of_list ["B"],Int 4) "S" "T" dbI

let dbJ' =
  let m = MapofRname.empty in
  let (sort_T,relation_T) = load_int_int
      ["B";"C"]  [(["B"],["C"])]
    [(1,1);
     (2,2);
     (4,3)] in
  let m = MapofRname.add "T" (sort_T,relation_T) m in 
  m

(* state based put *)
let dbI' = put_drop "D" (SetofAttr.of_list ["B"],Int 4) "S" "T" (dbJ',dbI)

let dT = 
    let relation_T  = instance "T" dbJ  in
    let relation_T' = instance "T" dbJ' in 
    change_set relation_T relation_T'

(* put by incremental lens *)
 let deltaS = delta_put_drop "S" dbI "D" (SetofAttr.of_list ["B"]) (Int 4) dT
					  
let relationS' =
  let ((_,_,_,fds),relationS) = MapofRname.find "S" dbI in
  relational_delta_merge relationS fds deltaS

(* two results agree *)
let _ =  SetofRecord.equal relationS' (instance "S" dbI')


(* state based lens composition test (Figure 1 in Bohannon et al.) *)

let l =
  join_dl ("Tracks","Albums") "Tracks1"  &:
  drop "Date" (["Track"],Int  9999) "Tracks1" "Tracks2" &:
  select "Tracks2" (PGt (PVar "Quantity",PCns (Int 2))) "Tracks3"

(* composite lens for normalized database *)
let l_norm =
  join_dl ("Track_Album","Track_Date_Rate") "Tracks"  &:
  join_dl ("Tracks","Albums") "Tracks1"  &:
  drop "Date" (["Track"],Int  9999) "Tracks1" "Tracks2" &:
  select "Tracks2" (PGt (PVar "Quantity",PCns (Int 2))) "Tracks3"
    
(* view : original view state *)
let view = get l db
    
let view_norm = get l_norm db_norm
    
(* convert key-value list to MapofRname.t.t *)
let mapofRname_of_list (l:(attr * 'a) list) : 'a MapofRname.t =
  List.fold_right (fun (k,v) -> MapofRname.add k v) l MapofRname.empty

(* static type (sort) inference of lens *)
let sort_view = qt_lens l (MapofRname.map fst db)
    
let sort_view_norm = qt_lens l_norm (MapofRname.map fst db_norm)
    
let view' = 
  let m = MapofRname.empty in
  let sort_Tracks3 = (SetofAttr.of_list ["Track";"Rating";"Album";"Quantity"],
		      mapofAttr_of_list [("Track",TStr);("Date",TInt);("Rating",TInt);
					("Album",TStr)],
		     (PGt (PVar "Quantity",PCns (Int 2))),
		     SetofFD.of_list
		       [(SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"]);
		        (SetofAttr.of_list ["Track"],SetofAttr.of_list ["Rating"])]) in
  let l_Tracks3 : (string * int * string * int) list =
    [("Lullaby", 4,"Show",3);
     ("Lovesong",5,"Disintegration",7);
   ] in 
  let tracks3 = List.fold_right (fun (t,r,a,q) ts ->
  SetofRecord.add
      (let m = MapofAttr.add "Track"    (Str t) MapofAttr.empty in
       let m = MapofAttr.add "Rating"   (Int r) m in
       let m = MapofAttr.add "Album"    (Str a) m in
       let m = MapofAttr.add "Quantity" (Int q) m in
       m)
      ts) l_Tracks3 SetofRecord.empty in
  let m = MapofRname.add "Tracks3" (sort_Tracks3,tracks3) m in 
  m

(* overall state-based putback *)
let db' = put l (view',db)

(* overall state-based putback into normalized base tables *)
let db_norm' = put l_norm (view',db_norm)    

(* fd violation check *)
let view'' = 
  let m = MapofRname.empty in
  let sort_Tracks3 = (SetofAttr.of_list ["Track";"Rating";"Album";"Quantity"],
		      mapofAttr_of_list [("Track",TStr);("Date",TInt);("Rating",TInt);
					("Album",TStr)],
		     (PGt (PVar "Quantity",PCns (Int 2))),
		     SetofFD.of_list
		       [(SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"]);
		        (SetofAttr.of_list ["Track"],SetofAttr.of_list ["Rating"])]) in
  let l_Tracks3 : (string * int * string * int) list =
    [("Lullaby", 4,"Show",3);
     ("Lovesong",5,"Paris",4);
     ("Trust",4,"Wish",5);
     ("Lullaby", 3,"Paris",4)
    ] in 
  let tracks3 = List.fold_right (fun (t,r,a,q) ts ->
  SetofRecord.add
      (let m = MapofAttr.add "Track"    (Str t) MapofAttr.empty in
       let m = MapofAttr.add "Rating"   (Int r) m in
       let m = MapofAttr.add "Album"    (Str a) m in
       let m = MapofAttr.add "Quantity" (Int q) m in
       m)
      ts) l_Tracks3 SetofRecord.empty in
  let m = MapofRname.add "Tracks3" (sort_Tracks3,tracks3) m in 
  m

let _ = try (ignore (put l (view'',db))) with
          Failure s -> Format.printf "Failure: %s@." s

(* overall incremental putback *)

let dTracks3 = 
    let relation_Tracks3  = instance "Tracks3" view  in
    let relation_Tracks3' = instance "Tracks3" view' in 
    change_set relation_Tracks3 relation_Tracks3'

let mChangeAlbum =
  delta_put_map l db (MapofRname.singleton "Tracks3" dTracks3)

let deltaTracks = MapofRname.find "Tracks" mChangeAlbum
let deltaAlbums = MapofRname.find "Albums" mChangeAlbum

let _ =
  let ((u,_,p,fdR),relation_r) = MapofRname.find "Tracks" db in
  let ((v,_,q,fdS),relation_s) = MapofRname.find "Albums" db in
  let relation_r' = relational_delta_merge relation_r fdR deltaTracks in
  let relation_s' = relational_delta_merge relation_s fdS deltaAlbums in
  SetofRecord.equal relation_r' (instance "Tracks" db') &&
  SetofRecord.equal relation_s' (instance "Albums" db')

(* test for intermediate steps of Figure 1 of Bohannon et al. *)

let db_Tracks2 = 
  let m = MapofRname.empty in
  let sort_Tracks2 = (SetofAttr.of_list ["Track";"Rating";"Album";"Quantity"],
		      mapofAttr_of_list [("Track",TStr);("Rating",TInt);
					("Album",TStr);("Quantity",TInt)],
		     PCns (Bol true),
		     SetofFD.of_list
		       [(SetofAttr.of_list ["Album"],SetofAttr.of_list ["Quantity"]);
		        (SetofAttr.of_list ["Track"],SetofAttr.of_list ["Rating"])]) in
  let l_Tracks2 : (string * int * string * int) list =
    [("Lullaby", 3,"Galore",        1);
     ("Lullaby", 3,"Show",          3);
     ("Lovesong",5,"Galore",        1);
     ("Lovesong",5,"Paris",         4);
     ("Trust",   4,"Wish",          5);
   ] in 
  let tracks2 = List.fold_right (fun (t,r,a,q) ts ->
  SetofRecord.add
      (let m = MapofAttr.add "Track"    (Str t) MapofAttr.empty in
       let m = MapofAttr.add "Rating"   (Int r) m in
       let m = MapofAttr.add "Album"    (Str a) m in
       let m = MapofAttr.add "Quantity" (Int q) m in
       m)
      ts) l_Tracks2 SetofRecord.empty in
  let m = MapofRname.add "Tracks2" (sort_Tracks2,tracks2) m in 
  m

(* put for select by state based lens *)
let db_Tracks2' = put (select "Tracks2" (PGt (PVar "Quantity",PCns (Int 2))) "Tracks3") (view',db_Tracks2)


(* put for select by incremental lens *)
 let deltaTracks2 = delta_put_select "Tracks2" db_Tracks2 (PGt (PVar "Quantity",PCns (Int 2))) dTracks3

let relationTracks2' =
  let ((_,_,_,fds),relationTracks2) = MapofRname.find "Tracks2" db_Tracks2  in
  relational_delta_merge relationTracks2 fds deltaTracks2

(* two results agree *)
let _ =  SetofRecord.equal relationTracks2' (instance "Tracks2" db_Tracks2')


let db_Tracks1 =
  let m = MapofRname.empty in
  let (sort_Tracks1,tracks1) = load_string_int_int_string_int 
    ["Track";"Date";"Rating";"Album";"Quantity"]
      [(["Album"],["Quantity"]);
       (["Track"],["Date";"Rating"])]
    [("Lullaby", 1989, 3,"Galore",        1);
     ("Lullaby", 1989, 3,"Show",          3);
     ("Lovesong",1989, 5,"Galore",        1);
     ("Lovesong",1989, 5,"Paris",         4);
     ("Trust",   1992, 4,"Wish",          5);
   ] in
  let m = MapofRname.add "Tracks1" (sort_Tracks1,tracks1) m in 
  m

let _ = get (drop "Date" (["Track"],Int 9999) "Tracks1" "Tracks2")
      db_Tracks1

let db_Tracks1' = put (drop "Date" (["Track"],Int 9999) "Tracks1" "Tracks2")
      (db_Tracks2',db_Tracks1)
let _ =          put_drop "Date" (SetofAttr.of_list ["Track"],Int 9999) "Tracks1" "Tracks2" (db_Tracks2',db_Tracks1)

(* put by incremental lens *)
 let deltaTracks1 = delta_put_drop "Tracks1" db_Tracks1 "Date" (SetofAttr.of_list ["Track"]) (Int 9999) deltaTracks2
					  
let relationTracks1' =
  let ((_,_,_,fds),relationTracks1) = MapofRname.find "Tracks1" db_Tracks1 in
  relational_delta_merge relationTracks1 fds deltaTracks1

(* two results agree *)
let _ =  SetofRecord.equal relationTracks1' (instance "Tracks1" db_Tracks1')

(* test with composition of last two spteps in Figure 1 of Bohannon et al. *)
let l_ds = 
  drop "Date" (["Track"],Int  9999) "Tracks1" "Tracks2" &:
  select "Tracks2" (PGt (PVar "Quantity",PCns (Int 2))) "Tracks3"

let dTracks1 =
  delta_put l_ds db_Tracks1 dTracks3

let relationTracks1' =
  let ((_,_,_,fds),relationTracks1) = MapofRname.find "Tracks1" db_Tracks1 in
  relational_delta_merge relationTracks1 fds dTracks1

let db_Tracks1' = put l_ds (view',db_Tracks1)

(* two results agree *)
let _ =  SetofRecord.equal relationTracks1' (instance "Tracks1" db_Tracks1')


(* test of first step (join) in Figure 1 of Bohannon et al. *)
let mChange = 
  let l1 = MapofRname.find "Tracks" db in
  let l2 = MapofRname.find "Albums" db in
  let ((u,_,p,fds1),_) = l1 in
  let ((v,_,q,fds2),_) = l2 in
  let j = SetofAttr.inter u v in
  let (dR,dS) = delta_put_join l1 l2 j (PCns (Bol true)) (PCns (Bol false)) 
	(SetofFD.union fds1 fds2) dTracks1 in
    MapofRname.add "Tracks" dR (MapofRname.singleton "Albums" dS)

let deltaTracks = MapofRname.find "Tracks" mChange
let deltaAlbums = MapofRname.find "Albums" mChange

let updated_db =
    put_join_dl "Tracks" "Albums" "Tracks1" (db_Tracks1',db)

(* two results agree *)
let _ =
  let ((u,_,p,fdR),relation_r) = MapofRname.find "Tracks" db in
  let ((v,_,q,fdS),relation_s) = MapofRname.find "Albums" db in
  let relation_r' = relational_delta_merge relation_r fdR deltaTracks in
  let relation_s' = relational_delta_merge relation_s fdS deltaAlbums in
  SetofRecord.equal relation_r' (instance "Tracks" updated_db) &&
  SetofRecord.equal relation_s' (instance "Albums" updated_db)




(* Figure 3.5 of Horn: *)
let dbRS =
 let (sort_R,relation_R) = load_int_int_int ["A";"B";"C"]
     [(["A"],["B"]); (["B"],["C"]);]
    [(2,1,1);
     (4,1,1);
     (5,3,1);
   ] in 
 let (sort_S,relation_S) = load_int_int
 ["C";"D"] [(["C"],["D"])]
    [(1,5);
   ] in
  MapofRname.add "R" (sort_R,relation_R)
    (MapofRname.singleton "S" (sort_S,relation_S))

let dbT = get_join_dl "R" "S" "T" dbRS

let dbT' =
  let (sort_T,relation_T) = load_int_int_int_int
      ["A";"B";"C";"D"]
      [(["A"],["B"]);
       (["B"],["C"]);
       (["C"],["D"]);
     ]
    [(3,2,2,6);
     (4,2,2,6);
     (5,3,2,6);
   ] in
  MapofRname.singleton "T" (sort_T,relation_T)


let deltaT = 
  let relation_T = instance "T" dbT in
  let relation_T'= instance "T" dbT' in
  change_set relation_T relation_T'

let mChange = 
  let l1 = MapofRname.find "R" dbRS in
  let l2 = MapofRname.find "S" dbRS in
  let ((u,_,p,fds1),_) = l1 in
  let ((v,_,q,fds2),_) = l2 in
  let j = SetofAttr.inter u v in
  let (dR,dS) = delta_put_join l1 l2 j (PCns (Bol true)) (PCns (Bol false)) 
	(SetofFD.union fds1 fds2) deltaT in
    MapofRname.add "R" dR (MapofRname.singleton "S" dS)

let deltaR = MapofRname.find "R" mChange
let deltaS = MapofRname.find "S" mChange

let dbRS' = put_join_dl "R" "S" "T" (dbT',dbRS)

(* two results agree *)
let _ =
  let ((u,_,p,fdR),relation_r) = MapofRname.find "R" dbRS in
  let ((v,_,q,fdS),relation_s) = MapofRname.find "S" dbRS in
  let relation_r' = relational_delta_merge relation_r fdR deltaR in
  let relation_s' = relational_delta_merge relation_s fdS deltaS in
  SetofRecord.equal relation_r' (instance "R" dbRS') &&
  SetofRecord.equal relation_s' (instance "S" dbRS')

(* transitive closure of functional dependencies *)
let _ = closure (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])
    (SetofFD.of_list [
         (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
         (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
         (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"]);])

let _ = closure (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"])
    (SetofFD.of_list [
         (SetofAttr.of_list ["A"],SetofAttr.of_list ["B"]);
         (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
         (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"]);])

let _ = closure (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"])
    (SetofFD.of_list [
         (SetofAttr.of_list ["A"],SetofAttr.of_list ["B";"B'"]);
         (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
         (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"]);])

(* functional dependencies that define given set of attributes *)
let _ = defining_fds  (SetofAttr.of_list ["C"])
    (SetofFD.of_list [
         (SetofAttr.of_list ["A"],SetofAttr.of_list ["B";"B'"]);
         (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
         (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"]);])

let _ = defining_fds  (SetofAttr.of_list ["D"])
    (SetofFD.of_list [
         (SetofAttr.of_list ["A"],SetofAttr.of_list ["B";"B'"]);
         (SetofAttr.of_list ["B"],SetofAttr.of_list ["C"]);
         (SetofAttr.of_list ["C"],SetofAttr.of_list ["D"]);])

(* join template test *)
let dbI =
  let m = MapofRname.empty in
  let (sort_R,relation_R) = load_string_string
      ["A";"B"] []
    [("a1", "b1");
     ("a1'","b1");
     ("a2", "b2");
   ] in
  let m = MapofRname.add "R" (sort_R,relation_R) m in
  let (sort_S,relation_S) = load_string
      ["B"] []
    [("b1");
     ("b2");
   ] in
  let m = MapofRname.add "S" (sort_S,relation_S) m 
  in m

let dbJ = get_join_dl "R" "S" "T" dbI
(*
{"T" -> (({A,B},{A -> string,  B -> string},true && true,{}),
  {{A -> "a1", B -> "b1"},
   {A -> "a1'",B -> "b1"},
   {A -> "a2", B -> "b2"}}

 *)

let dbJ' = 
  let (sortT,instanceT) = MapofRname.find "T" dbJ in
  let l_T : (string*string) list =
    [("a1", "b1");
  (* ("a1'","b1"); *) (* deleted *)
  (* ("a2","b2");  *) (* deleted *)
   ] in
  let relationT = List.fold_right (fun (a,b) ts ->
    SetofRecord.add
      (let m = MapofAttr.empty in
       let m = MapofAttr.add "A" (Str a) m in
       let m = MapofAttr.add "B" (Str b) m in
       m
      )
      ts) l_T SetofRecord.empty in
  let m = MapofRname.add "T" (sortT,relationT) dbJ in 
  m

let dbI' =  put_join_template ("R",(PCns (Bol true))) ("S",(PCns (Bol false))) "T" (dbJ',dbI)
let dbI' =  put_join_template ("R",(PCns (Bol false))) ("S",(PCns (Bol true))) "T" (dbJ',dbI)
let dbI' =  put_join_template ("R",(PCns (Bol true))) ("S",(PCns (Bol true))) "T" (dbJ',dbI)
