
let min (compare: 'a -> 'a -> int) (x: 'a) (y: 'a) =
  if compare x y >= 0
  then y
  else x

let max (compare: 'a -> 'a -> int) (x: 'a) (y: 'a) =
  if compare x y >= 0
  then x
  else y

type day = Mo | Tu | We | Th | Fr | Sa | Su

let string_of_day (d : day) : string =
  match d with
  | Mo -> "Mo"
  | Tu -> "Tu"
  | We -> "We"
  | Th -> "Th"
  | Fr -> "Fr"
  | Sa -> "Sa"
  | Su -> "Su"

let day_of_string_opt (s : string) : day option =
  match s with
  | "Mo" -> Some Mo
  | "Tu" -> Some Tu
  | "We" -> Some We
  | "Th" -> Some Th
  | "Fr" -> Some Fr
  | "Sa" -> Some Sa
  | "Su" -> Some Su
  | _ -> None

let int_of_day (d : day) : int =
  match d with
  | Mo -> 0
  | Tu -> 1
  | We -> 2
  | Th -> 3
  | Fr -> 4
  | Sa -> 5
  | Su -> 6

let compare_day (d1 : day) (d2 : day) : int =
  Int.compare (int_of_day d1) (int_of_day d2)

type hour = int

let string_of_hour (h : hour) : string =
  (if h < 10 then "0" else "") ^ string_of_int h

let hour_of_string_opt (s : string) : hour option =
  match int_of_string_opt s with
  | Some h ->
     if h >= 0 && h <= 24
     then Some h
     else None
  | None -> None

let compare_hour : hour -> hour -> int = Int.compare

type minute = M00 | M15 | M30 | M45

let string_of_minute (m : minute) : string =
  match m with
  | M00 -> "00"
  | M15 -> "15"
  | M30 -> "30"
  | M45 -> "45"

let minute_of_string_opt (s : string) : minute option =
  match s with
  | "00" -> Some M00
  | "15" -> Some M15
  | "30" -> Some M30
  | "45" -> Some M45
  | _ -> None

let int_of_minute (m : minute) : int =
  match m with
  | M00 -> 0
  | M15 -> 1
  | M30 -> 2
  | M45 -> 3

let compare_minute (m1 : minute) (m2 : minute) : int =
  Int.compare (int_of_minute m1) (int_of_minute m2)


type time =
  {
    hour : int;
    minute : minute;
  }

let time_of_string_opt (s : string) : time option =
  if String.length s = 5 && s.[2] = ':'
  then
    let h = hour_of_string_opt (String.sub s 0 2) in
    let m = minute_of_string_opt (String.sub s 3 2) in
    match h, m with
    | Some h, Some m ->
       if h = 24 && m <> M00
       then None
       else Some {hour=h;minute=m}
    | _ -> None
  else None

let string_of_time (t : time) : string =
  string_of_hour t.hour
  ^ ":"
  ^ string_of_minute t.minute

let compare_time (t1 : time) (t2 : time) : int =
  let ch = compare_hour t1.hour t2.hour in
  if ch = 0
  then compare_minute t1.minute t2.minute
  else ch

type interval =
  {
    day : day;
    start_time : time;
    end_time : time;
  }

let string_of_interval (i : interval) : string =
  string_of_day i.day
  ^ "  "
  ^ string_of_time i.start_time
  ^ "--"
  ^ string_of_time i.end_time

let interval_of_string_opt (s : string) : interval option =
  let day = day_of_string_opt (String.sub s 0 2) in
  let s = String.trim (String.sub s 2 (String.length s - 2)) in
  if (String.length s = 12) && (String.sub s 5 2 = "--")
  then
    let start_time = time_of_string_opt (String.sub s 0 5) in
    let end_time = time_of_string_opt (String.sub s 7 5) in
    match day, start_time, end_time with
    | Some day, Some start_time, Some end_time ->
       Some {day;start_time;end_time}
    | _ -> None
  else None

let is_empty (i : interval) : bool =
  compare_time i.start_time i.end_time >= 0

let compare_interval (i1 : interval) (i2 : interval) : int =
  let cd = compare_day i1.day i2.day in
  if cd = 0
  then compare_time i1.start_time i2.start_time
  else cd

type schedule = interval list

let intersect_i_i (i1: interval) (i2: interval) : interval option =
  if i1.day = i2.day
  then
    let day = i1.day in
    let start_time = max compare_time i1.start_time i2.start_time in
    let end_time = min compare_time i1.end_time i2.end_time in
    let interval = {day;start_time;end_time} in
    if is_empty interval
    then None
    else Some interval
  else None

let intersect_s_i (s : schedule) (i: interval) : schedule =
  List.filter_map (intersect_i_i i) s

let intersect_s_s (s1 : schedule) (s2: schedule) : schedule =
  List.fold_left (fun acc i -> (intersect_s_i s1 i) @ acc) [] s2

let all_time : schedule =
  let all_day d =
    {
      day = d;
      start_time={hour=0;minute=M00};
      end_time={hour=24;minute=M00};
    }
  in
  List.map all_day [Mo;Tu;We;Th;Fr;Sa;Su]

let intersect_schedules (s : schedule list) : schedule =
  List.fold_left intersect_s_s all_time s
