(*
A Domain Name client library.
This code is placed in the Public Domain.

References:
ftp://ftp.rfc-editor.org/in-notes/rfc1035.txt
http://pleac.sourceforge.net/pleac_ocaml/sockets.html
http://www.brool.com/index.php/ocaml-sockets
http://www.zenskg.net/mdns_article/mdns_article.html
*)

type int16  = int
type byte   = int
type bytes  = string

type label        = bytes
type domain_name  = bytes

let re_dot = Str.regexp_string "."

let split_domain (name : domain_name) = Str.split re_dot name

module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val bind   : ('a -> 'b t) -> ('a t -> 'b t)
  val fail   : 'a t
end

module Monad (M : MONAD) = struct
  include M
  let (>>=) m f = bind f m
  let fmap f = bind (fun x -> return (f x))
  let (>>) m m' = m >>= fun _ -> m'
  let guard p = if p then return () else fail
end

module Parser = struct
  type cursor = string * int

  type 'a parser = Parser of (cursor -> 'a option * cursor)

  include Monad (struct
    type 'a t = 'a parser
    let return x = Parser (fun cur -> (Some x, cur))
    let bind f (Parser p) = Parser (fun cur ->
      match p cur with
      | (None  , _  ) -> (None, cur)
      | (Some x, cur) -> let Parser q = f x in q cur)
    let fail = Parser (fun cur -> (None, cur))
  end)

  let run (Parser p) str = let (res, _) = p (str, 0) in res
 
  (* Current position as state: parsers are monads in more than one way *)
  let tell     = Parser (fun (_, pos as cur) -> (Some pos, cur))
  let seek off = Parser (fun (str, _ as cur) ->
    if 0 <= off && off <= String.length str
    then (Some (), (str, off))
    else (None, cur) )

  (* Zero-width assertion: parse, backtrack and succeed on success *)
  let ensure (Parser p) = Parser (fun cur ->
    match p cur with
    | (Some _, _) -> (Some (), cur)
    | (None  , _) -> (None   , cur) )

  (* Turn a failure into a list of successes: repeat parser until failure *)
  let sequence (Parser p) =
    let rec go xs cur = match p cur with
    | (None  , cur)          -> (Some (List.rev xs), cur)
    | (Some x, cur)          -> go (x :: xs) cur
    in Parser (go [])

  let repeat n (Parser p) = Parser (fun bak ->
    let rec go n xs cur =
      if n = 0 then (Some (List.rev xs), cur) else
      match p cur with
      | (None  , _  ) -> (None, bak)
      | (Some x, cur) -> go (pred n) (x :: xs) cur
    in go n [] bak )

  let eof = Parser (fun (str, pos as cur) ->
    ((if pos = String.length str then Some () else None), cur) )

  let next = Parser (fun (str, pos as cur) ->
    if pos = String.length str then (None, cur) else
    (Some str.[pos], (str, succ pos)) )

  let take n = Parser (fun (str, pos as cur) ->
    if 0 <= n && n <= String.length str - pos
      then (Some (String.sub str pos n), (str, pos + n))
      else (None, cur) )
end

let byte : byte Parser.t = Parser.(fmap int_of_char next)

let bytes cnt : bytes Parser.t = Parser.take cnt

let int16 : int16 Parser.t = 
  let open Parser in
  byte >>= fun hi ->
  byte >>= fun lo ->
  return ((hi lsl 8) lor lo)

let int32 : int32 Parser.t =
  let open Parser in
  let (<|) m n = Int32.logor (Int32.shift_left m 8) (Int32.of_int n) in
  byte >>= fun b0 ->
  byte >>= fun b1 ->
  byte >>= fun b2 ->
  byte >>= fun b3 ->
  return (((Int32.of_int b0 <| b1) <| b2) <| b3)

(* Parsers are monadic, pretty-printers are monoidal *)
module type MONOID = sig
  type 'a t
  val zero : 'a t
  val plus : 'a t -> 'a t -> 'a t
end

module Monoid (M : MONOID) = struct
  include M
  let (++) = plus
  let sequence f xs = List.fold_left (fun ms x -> ms ++ f x) zero xs
  let concat ms = sequence (fun x -> x) ms
end

module Writer = struct
  type writer = Writer of (Buffer.t -> unit)
  include Monoid (struct
    type 'a t = writer
    let zero = Writer (fun _ -> ())
    let plus (Writer p) (Writer q) = Writer (fun buf -> p buf; q buf)
  end)

  let run (Writer p) : bytes =
    let buf = Buffer.create 256 in
    p buf; Buffer.contents buf

  let char c = Writer (fun buf -> Buffer.add_char buf c)

  let byte (n : byte) = char (char_of_int n)

  let bytes (s : bytes) = Writer (fun buf -> Buffer.add_string buf s)

  let int16 (n : int16) = Writer (fun buf ->
    Buffer.add_char buf (char_of_int ((n lsr  8) land 255));
    Buffer.add_char buf (char_of_int ( n         land 255)) )

  let int32 (n : int32) = Writer (fun buf ->
    Buffer.add_char buf (char_of_int (Int32.to_int (Int32.logand (Int32.shift_right n 24) 255l)));
    Buffer.add_char buf (char_of_int (Int32.to_int (Int32.logand (Int32.shift_right n 16) 255l)));
    Buffer.add_char buf (char_of_int (Int32.to_int (Int32.logand (Int32.shift_right n  8) 255l)));
    Buffer.add_char buf (char_of_int (Int32.to_int (Int32.logand                    n     255l))) )
end

let write_bytes (str : bytes) =
  let len = String.length str in
  if len > 255 then invalid_arg "write_bytes" else
  Writer.(byte len ++ bytes str)

let parse_bytes = Parser.(byte >>= bytes)

let write_label (lbl : label) =
  let len = String.length lbl in
  if len > 63 then invalid_arg "write_label" else
  Writer.(byte len ++ bytes lbl)

let parse_label : label Parser.t =
  let open Parser in
  ensure (byte >>= fun n -> guard (0 < n && n < 64)) >> byte >>= bytes

let write_domain_name (name : domain_name) =
  let labels = split_domain name in
  Writer.(sequence write_label labels ++ byte 0)

let parse_domain_name : domain_name Parser.t =
 let open Parser in
 let rec labels () =
    sequence parse_label       >>= fun ls  ->
    byte                       >>= fun n   ->
    if n = 0 then return ls else
    guard (n land 0xc0 = 0xc0) >>
    byte                       >>= fun m   ->
    let off = ((n land 0x3f) lsl 8) lor m in
    tell                       >>= fun pos ->
    seek off                   >>
    labels ()                  >>= fun ls' ->
    seek pos                   >>
    return (ls @ ls')
  in fmap (String.concat ".") $ labels ()

type rr_type = [
| `A | `NS | `MD | `MF | `CNAME | `SOA | `MB | `MG
| `MR | `NULL | `WKS | `PTR | `HINFO | `MINFO | `MX | `TXT
]

type q_type = [ rr_type | `AXFR | `MAILB | `MAILA | `ANY ]

let int_of_rr_type : rr_type -> int = function
| `A     ->  1
| `NS    ->  2
| `MD    ->  3
| `MF    ->  4
| `CNAME ->  5
| `SOA   ->  6
| `MB    ->  7
| `MG    ->  8
| `MR    ->  9
| `NULL  -> 10
| `WKS   -> 11
| `PTR   -> 12
| `HINFO -> 13
| `MINFO -> 14
| `MX    -> 15
| `TXT   -> 16

and rr_type_of_int : int -> rr_type = function
|  1     -> `A
|  2     -> `NS
|  3     -> `MD
|  4     -> `MF
|  5     -> `CNAME
|  6     -> `SOA
|  7     -> `MB
|  8     -> `MG
|  9     -> `MR
| 10     -> `NULL
| 11     -> `WKS
| 12     -> `PTR
| 13     -> `HINFO
| 14     -> `MINFO
| 15     -> `MX
| 16     -> `TXT
| _      -> invalid_arg "rr_type_of_int"

let int_of_q_type : q_type -> int = function
| `AXFR         -> 252
| `MAILB        -> 253
| `MAILA        -> 254
| `ANY          -> 255
| #rr_type as t -> int_of_rr_type t

and q_type_of_int : int -> q_type = function
| 252           -> `AXFR
| 253           -> `MAILB
| 254           -> `MAILA
| 255           -> `ANY
| n             -> (rr_type_of_int n :> q_type)

type rr_class = [ `IN | `CS | `CH | `HS ]

type q_class = [ rr_class | `ANY ]

let int_of_rr_class : rr_class -> int = function
| `IN -> 1
| `CS -> 2
| `CH -> 3
| `HS -> 4

and rr_class_of_int : int -> rr_class = function
| 1   -> `IN
| 2   -> `CS
| 3   -> `CH
| 4   -> `HS
| _   -> invalid_arg "rr_class_of_int"

let int_of_q_class : q_class -> int = function
| `ANY           -> 255
| #rr_class as c -> int_of_rr_class c

and q_class_of_int : int -> q_class = function
| 255            -> `ANY
| n              -> (rr_class_of_int n :> q_class)

type resource = [
| `Hostinfo  of string * string
| `Domain    of domain_name
| `Mailbox   of domain_name * domain_name
| `Exchange  of int * domain_name
| `Data      of bytes
| `Text      of bytes list
| `Authority of domain_name * domain_name * int32 * int32 * int32 * int32 * int32
| `Address   of Unix.inet_addr
| `Services  of int32 * byte * bytes
]

let write_resource =
  let open Writer in function
  | `Hostinfo (cpu, os) ->
       write_bytes       cpu
    ++ write_bytes       os
  | `Domain name ->
       write_domain_name name
  | `Mailbox  (rmbx, embx) ->
       write_domain_name rmbx
    ++ write_domain_name embx
  | `Exchange (pref, exch) ->
       int16             pref
    ++ write_domain_name exch
  | `Data data ->
       bytes             data
  | `Text texts ->
    sequence write_bytes texts
  | `Authority (mname, rname, serial, refresh, retry, expire, minimum) ->
       write_domain_name mname
    ++ write_domain_name rname
    ++ int32             serial
    ++ int32             refresh
    ++ int32             retry
    ++ int32             expire
    ++ int32             minimum
  | `Address addr ->
       int32  (Obj.magic addr : int32)
  | `Services (addr, proto, bmap) ->
       int32             addr
    ++ byte              proto
    ++ bytes             bmap

let parse_resource rr_type rr_dlen =
  let open Parser in match rr_type with
  | `HINFO ->
    parse_bytes                >>= fun cpu ->
    parse_bytes                >>= fun os  ->
    return (`Hostinfo (cpu, os))
  | `MB | `MD | `MF | `MG | `MR | `NS
  | `CNAME | `PTR ->
    parse_domain_name          >>= fun name ->
    return (`Domain name)
  | `MINFO ->
    parse_domain_name          >>= fun rmailbx ->
    parse_domain_name          >>= fun emailbx ->
    return (`Mailbox (rmailbx, emailbx))
  | `MX ->
    int16                      >>= fun preference ->
    parse_domain_name          >>= fun exchange   ->
    return (`Exchange (preference, exchange))
  | `NULL ->
    bytes rr_dlen              >>= fun data ->
    return (`Data data)
  | `TXT ->
    sequence (byte >>= bytes)  >>= fun texts ->
    return (`Text texts)
  | `SOA ->
    parse_domain_name          >>= fun mname   ->
    parse_domain_name          >>= fun rname   ->
    int32                      >>= fun serial  ->
    int32                      >>= fun refresh ->
    int32                      >>= fun retry   ->
    int32                      >>= fun expire  ->
    int32                      >>= fun minimum ->
    return (`Authority (mname, rname, serial, refresh, retry, expire, minimum))
  | `A ->
    int32                      >>= fun addr ->
    return (`Address  (Obj.magic addr : Unix.inet_addr))
  | `WKS ->
    int32                      >>= fun addr   ->
    byte                       >>= fun proto  ->
    bytes (rr_dlen-5)          >>= fun bitmap ->
    return (`Services (addr, proto, bitmap))

type rsrc_record = {
  rr_name  : domain_name;
  rr_type  : rr_type;
  rr_class : rr_class;
  rr_ttl   : int32;
  rr_rdata : resource;
}

let write_rsrc_record r =
  let open Writer in
  let rr_rdata = run (write_resource r.rr_rdata) in
     write_domain_name      r.rr_name
  ++ int16 (int_of_rr_type  r.rr_type)
  ++ int16 (int_of_rr_class r.rr_class)
  ++ int32                  r.rr_ttl
  ++ int16     (String.length rr_rdata)
  ++ bytes                    rr_rdata

let parse_rsrc_record =
  let open Parser in
  parse_domain_name              >>= fun rr_name  ->
  fmap rr_type_of_int  int16     >>= fun rr_type  ->
  fmap rr_class_of_int int16     >>= fun rr_class ->
  int32                          >>= fun rr_ttl   ->
  int16                          >>= fun rr_dlen  ->
  parse_resource rr_type rr_dlen >>= fun rr_rdata ->
  return { rr_name; rr_type; rr_class; rr_ttl; rr_rdata; }

type question = {
  q_name  : domain_name;
  q_type  : q_type;
  q_class : q_class;
}
 
let write_question q =
  let open Writer in
     write_domain_name     q.q_name
  ++ int16 (int_of_q_type  q.q_type )
  ++ int16 (int_of_q_class q.q_class)

let parse_question =
  let open Parser in
  parse_domain_name         >>= fun q_name  ->
  fmap q_type_of_int  int16 >>= fun q_type  ->
  fmap q_class_of_int int16 >>= fun q_class ->
  return { q_name; q_type; q_class; }

type dns_record = {
  id         : int16;
  detail     : int16;
  question   : question    list;
  answer     : rsrc_record list;
  authority  : rsrc_record list;
  additional : rsrc_record list;
}

let write_dns_record d =
  let open Writer in
     int16                      d.id
  ++ int16                      d.detail
  ++ int16 (List.length         d.question  )
  ++ int16 (List.length         d.answer    )
  ++ int16 (List.length         d.authority )
  ++ int16 (List.length         d.additional)
  ++ sequence write_question    d.question
  ++ sequence write_rsrc_record d.answer
  ++ sequence write_rsrc_record d.authority
  ++ sequence write_rsrc_record d.additional

let parse_dns_record =
  let open Parser in
  int16                            >>= fun id         ->
  int16                            >>= fun detail     ->
  int16                            >>= fun qdcount    ->
  int16                            >>= fun ancount    ->
  int16                            >>= fun nscount    ->
  int16                            >>= fun arcount    ->
  repeat qdcount parse_question    >>= fun question   ->
  repeat ancount parse_rsrc_record >>= fun answer     ->
  repeat nscount parse_rsrc_record >>= fun authority  ->
  repeat arcount parse_rsrc_record >>= fun additional ->
  return { id; detail; question; answer; authority; additional; }

let query ?(q_type=`A) id q_name =
  if id land 0xffff <> id then invalid_arg "query" else {
  id;
  detail     = 0b0_0000_0010_000_0000;
  question   = [ { q_name; q_type; q_class = `IN; } ];
  answer     = [];
  authority  = [];
  additional = []; }

let unwind ~protect f x =
  try
    let y  = f x in
    let () = protect x in
    y
  with e ->
    let () = protect x in
    raise e
  
let dns_port  = (Unix.getservbyname "domain" "udp").Unix.s_port

let query_dns addr q =
  let len = 4096 in
  let buf  = String.create len in
  let msg  = Writer.run (write_dns_record q) in
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM 0 in
  let peer = Unix.ADDR_INET (Unix.inet_addr_of_string addr, dns_port) in
  unwind ~protect:Unix.close (fun sock ->
    Unix.setsockopt_float sock Unix.SO_RCVTIMEO  1.;
    let _ = Unix.sendto sock msg 0 (String.length msg) [] peer in
    let cnt, _ = Unix.recvfrom sock buf 0 len [] in
    match Parser.run parse_dns_record (String.sub buf 0 cnt) with
    | Some dns -> dns
    | None     -> failwith "Parse error"
  ) sock

let mail_servers server domain =
  let res = query_dns server (query ~q_type:`MX 0 domain) in
  (List.sort (fun (p, _) (p', _) -> compare p p')
  (List.map (function { rr_rdata = `Exchange (p, d); _ } -> (p, d))
  (List.filter (fun { rr_type; _ } -> rr_type = `MX)
  res.answer)))
