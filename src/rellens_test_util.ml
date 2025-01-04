open Rellens_types
open Print
open Rellens

(* database loading utilities *)
let load_fd (x:attr list) (y:attr list) : fd =
  (SetofAttr.of_list x,SetofAttr.of_list y)

let load_fds (l: ((attr list) * (attr list)) list) : SetofFD.t =
  SetofFD.of_list (List.map (fun (x,y) -> load_fd x y) l)

(* convert key-value list to MapofAttr.t *)
let mapofAttr_of_list (l:(attr * 'a) list) : 'a MapofAttr.t =
  List.fold_right (fun (k,v) -> MapofAttr.add k v) l MapofAttr.empty

(* load relation with schema information provided for each combination *)
let load_string_int (attrs: attr list) (fdl: ((attr list) * (attr list)) list)
    (l: (string*int) list) : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let tenv = mapofAttr_of_list [(a1,TStr);
				(a2,TInt);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    let m = MapofAttr.add a2 (Int v2) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_string_string_string (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (string*string*string) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let tenv = mapofAttr_of_list [(a1,TStr);(a2,TStr);(a3,TStr);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    let m = MapofAttr.add a2 (Str v2) m in
    let m = MapofAttr.add a3 (Str v3) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_string_string_string_int (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (string*string*string*int) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let a4 = List.nth attrs 3 in
  let tenv = mapofAttr_of_list [(a1,TStr);(a2,TStr);(a3,TStr);(a4,TInt)] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3,v4) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    let m = MapofAttr.add a2 (Str v2) m in
    let m = MapofAttr.add a3 (Str v3) m in
    let m = MapofAttr.add a4 (Int v4) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)


let load_string_string_string_int_string (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (string*string*string*int*string) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let a4 = List.nth attrs 3 in
  let a5 = List.nth attrs 4 in
  let tenv = mapofAttr_of_list [(a1,TStr);(a2,TStr);(a3,TStr);(a4,TInt);(a5,TStr)] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3,v4,v5) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    let m = MapofAttr.add a2 (Str v2) m in
    let m = MapofAttr.add a3 (Str v3) m in
    let m = MapofAttr.add a4 (Int v4) m in
    let m = MapofAttr.add a5 (Str v5) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_string_string (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (string*string) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let tenv = mapofAttr_of_list [(a1,TStr);(a2,TStr);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    let m = MapofAttr.add a2 (Str v2) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_string (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: string list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let tenv = mapofAttr_of_list [(a1,TStr);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_int_int (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (int*int) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let tenv = mapofAttr_of_list [(a1,TInt);(a2,TInt);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Int v1) m in
    let m = MapofAttr.add a2 (Int v2) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_int_int_int (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (int*int*int) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let tenv = mapofAttr_of_list [(a1,TInt);(a2,TInt);(a3,TInt);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Int v1) m in
    let m = MapofAttr.add a2 (Int v2) m in
    let m = MapofAttr.add a3 (Int v3) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_int_int_int_int (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (int*int*int*int) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let a4 = List.nth attrs 3 in
  let tenv = mapofAttr_of_list [(a1,TInt);(a2,TInt);(a3,TInt);(a4,TInt)] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3,v4) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Int v1) m in
    let m = MapofAttr.add a2 (Int v2) m in
    let m = MapofAttr.add a3 (Int v3) m in
    let m = MapofAttr.add a4 (Int v4) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_string_int_int_string_int (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (string*int*int*string*int) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let a4 = List.nth attrs 3 in
  let a5 = List.nth attrs 4 in
  let tenv = mapofAttr_of_list [(a1,TStr);(a2,TInt);(a3,TInt);(a4,TStr);(a5,TInt)] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3,v4,v5) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Str v1) m in
    let m = MapofAttr.add a2 (Int v2) m in
    let m = MapofAttr.add a3 (Int v3) m in
    let m = MapofAttr.add a4 (Str v4) m in
    let m = MapofAttr.add a5 (Int v5) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)

let load_int_string_int (attrs: attr list)
    (fdl: ((attr list) * (attr list)) list)
    (l: (int*string*int) list)
   : (sort*relation) =
  let u  = SetofAttr.of_list attrs in
  let a1 = List.nth attrs 0 in
  let a2 = List.nth attrs 1 in
  let a3 = List.nth attrs 2 in
  let tenv = mapofAttr_of_list [(a1,TInt);(a2,TStr);(a3,TInt);] in
  let fds = load_fds fdl in
  let relation = List.fold_right (fun (v1,v2,v3) ->
    let m = MapofAttr.empty in
    let m = MapofAttr.add a1 (Int v1) m in
    let m = MapofAttr.add a2 (Str v2) m in
    let m = MapofAttr.add a3 (Int v3) m in
    SetofRecord.add m) l SetofRecord.empty in
  ((u,tenv,(PCns (Bol true)),fds),relation)
