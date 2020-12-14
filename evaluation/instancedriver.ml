open Instance

let results = lex rus code

let rec to_string s =
match s with
| [] -> ""
| h::t -> if h = A then ("A" ^ (to_string t)) else ("B" ^ (to_string t))

let rec token_to_string token =
match token with
| label, pref -> "(" ^ (to_string label) ^ ", " ^ (to_string pref) ^ ")"

let rec tokens_to_string tokens =
match tokens with
| [] -> ""
| t::[] -> (token_to_string t)
| t::ts -> (token_to_string t) ^ ", " ^ (tokens_to_string ts)

let rec print_results rs =
match rs with
| ts, rest -> Printf.printf "Tokens: %s\n" (tokens_to_string ts) ; Printf.printf "Rest: %s\n" (to_string rest)

let () = Printf.printf "Code: %s\n" (to_string code)
let () = print_results results
