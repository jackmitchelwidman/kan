(* ============================================================================
   Bigint — minimal arbitrary-precision integers (sign + magnitude, base 10^9).
   ----------------------------------------------------------------------------
   Kan's `Integer` is unbounded, like Python's `int`. OCaml's stdlib has no
   bignum and Kan takes no third-party dependencies, so we hand-roll a small,
   correct one: enough for exact arithmetic (+, -, *, compare), which is what a
   machine-backed integer for *computation* needs. `Nat` stays the inductive
   type for proofs; `Integer` is the one you compute large values with.

   Representation: sign ∈ {-1,0,1}; magnitude is little-endian base 10^9 with no
   high zero limbs; the integer 0 is uniquely {sign=0; mag=[||]}. Base 10^9 keeps
   single-limb products (< 10^18) inside a 63-bit OCaml int and a C int64, so the
   *same* algorithm ports to the C backend unchanged.
   ========================================================================== *)

type t = { sign : int; mag : int array }

let base = 1_000_000_000
let zero = { sign = 0; mag = [||] }

(* strip high zero limbs; return the canonical form *)
let mk sign mag =
  let n = ref (Array.length mag) in
  while !n > 0 && mag.(!n - 1) = 0 do decr n done;
  if !n = 0 then zero
  else { sign; mag = (if !n = Array.length mag then mag else Array.sub mag 0 !n) }

let of_int (i : int) : t =
  if i = 0 then zero
  else
    let s = if i < 0 then -1 else 1 in
    let n = ref (abs i) and ds = ref [] in
    while !n > 0 do ds := (!n mod base) :: !ds; n := !n / base done;
    mk s (Array.of_list (List.rev !ds))

(* parse a decimal string, optional leading '-' *)
let of_string (str : string) : t =
  let str, s = if String.length str > 0 && str.[0] = '-' then (String.sub str 1 (String.length str - 1), -1) else (str, 1) in
  let len = String.length str in
  if len = 0 then zero
  else begin
    let ds = ref [] in           (* built most-significant-first, reversed at the end *)
    let i = ref len in
    while !i > 0 do
      let lo = if !i - 9 < 0 then 0 else !i - 9 in
      ds := int_of_string (String.sub str lo (!i - lo)) :: !ds;
      i := lo
    done;
    mk s (Array.of_list (List.rev !ds))
  end

let to_string (x : t) : string =
  if x.sign = 0 then "0"
  else begin
    let buf = Buffer.create 24 in
    if x.sign < 0 then Buffer.add_char buf '-';
    let n = Array.length x.mag in
    Buffer.add_string buf (string_of_int x.mag.(n - 1));
    for j = n - 2 downto 0 do Buffer.add_string buf (Printf.sprintf "%09d" x.mag.(j)) done;
    Buffer.contents buf
  end

(* unsigned magnitude comparison: -1 / 0 / 1 *)
let cmp_mag a b =
  let la = Array.length a and lb = Array.length b in
  if la <> lb then compare la lb
  else
    let rec go i = if i < 0 then 0 else if a.(i) <> b.(i) then compare a.(i) b.(i) else go (i - 1) in
    go (la - 1)

let add_mag a b =
  let la = Array.length a and lb = Array.length b in
  let n = if la > lb then la else lb in
  let r = Array.make (n + 1) 0 and carry = ref 0 in
  for i = 0 to n - 1 do
    let s = (if i < la then a.(i) else 0) + (if i < lb then b.(i) else 0) + !carry in
    r.(i) <- s mod base; carry := s / base
  done;
  r.(n) <- !carry;
  r

(* precondition: a >= b (unsigned) *)
let sub_mag a b =
  let la = Array.length a and lb = Array.length b in
  let r = Array.make la 0 and borrow = ref 0 in
  for i = 0 to la - 1 do
    let s = a.(i) - (if i < lb then b.(i) else 0) - !borrow in
    if s < 0 then (r.(i) <- s + base; borrow := 1) else (r.(i) <- s; borrow := 0)
  done;
  r

let mul_mag a b =
  let la = Array.length a and lb = Array.length b in
  if la = 0 || lb = 0 then [||]
  else begin
    let r = Array.make (la + lb) 0 in
    for i = 0 to la - 1 do
      let carry = ref 0 in
      for j = 0 to lb - 1 do
        let cur = r.(i + j) + (a.(i) * b.(j)) + !carry in
        r.(i + j) <- cur mod base; carry := cur / base
      done;
      r.(i + lb) <- r.(i + lb) + !carry
    done;
    r
  end

let neg x = if x.sign = 0 then zero else { x with sign = - x.sign }

let add x y =
  if x.sign = 0 then y
  else if y.sign = 0 then x
  else if x.sign = y.sign then mk x.sign (add_mag x.mag y.mag)
  else
    let c = cmp_mag x.mag y.mag in
    if c = 0 then zero
    else if c > 0 then mk x.sign (sub_mag x.mag y.mag)
    else mk y.sign (sub_mag y.mag x.mag)

let sub x y = add x (neg y)
let mul x y = if x.sign = 0 || y.sign = 0 then zero else mk (x.sign * y.sign) (mul_mag x.mag y.mag)

let compare x y =
  if x.sign <> y.sign then compare x.sign y.sign
  else if x.sign = 0 then 0
  else let c = cmp_mag x.mag y.mag in if x.sign > 0 then c else - c

let equal x y = compare x y = 0
