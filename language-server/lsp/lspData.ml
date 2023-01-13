module Position = struct
  
  type t = { line : int; char : int; }

  let compare pos1 pos2 =
    match Int.compare pos1.line pos2.line with
    | 0 -> Int.compare pos1.char pos2.char
    | x -> x

  let to_string pos = Format.sprintf "(%i,%i)" pos.line pos.char

end

module Range = struct
  type t = { start : Position.t; stop : Position.t; }
end 

type diagnostic = {
  range : Range.t;
  message : string;
  severity : Feedback.level;
}
