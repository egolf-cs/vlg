open Instance

let to_string chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let to_chars s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let read_whole_file filename =
    let ch = open_in filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let code = to_chars (read_whole_file "data.txt")
let results = lex rus code

let rec token_to_string token =
match token with
| label, pref -> "(" ^ (to_string label) ^ ", " ^ (to_string pref) ^ ")"

let rec tokens_to_string tokens =
match tokens with
| [] -> ""
| t::[] -> (token_to_string t)
| t::ts -> (token_to_string t) ^ ",\n" ^ (tokens_to_string ts)

let rec print_results rs =
match rs with
| ts, rest -> Printf.printf "Tokens: %s\n" (tokens_to_string ts) ; Printf.printf "Rest: %s\n" (to_string rest)


let () = Printf.printf "Code: %s\n" (to_string code)
let () = print_results results
