(*
 * Copyright (c) 2011 Richard Mortier <mort@cantab.net>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

(* DNS related portions of this from:

   A Domain Name client library.  This code is placed in the Public
   Domain.

   References:
   ftp://ftp.rfc-editor.org/in-notes/rfc1035.txt
   http://pleac.sourceforge.net/pleac_ocaml/sockets.html
   http://www.brool.com/index.php/ocaml-sockets
   http://www.zenskg.net/mdns_article/mdns_article.html
*)

let sp = Printf.sprintf
let pr = Printf.printf
let ep = Printf.eprintf
let int_of_byte b = int_of_char b

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
  let ($) x = x
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

  let run (Parser p) str pos = 
    p (str, pos)
 
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
  Parser.(
    byte >>= fun lo ->
    byte >>= fun hi ->
    return ((hi lsl 8) lor lo)
  )
(*
let int32 : int32 Parser.t =
  Parser.(
    let (<|) m n = Int32.logor (Int32.shift_left m 8) (Int32.of_int n) in
    byte >>= fun b0 ->
    byte >>= fun b1 ->
    byte >>= fun b2 ->
    byte >>= fun b3 ->
    return (((Int32.of_int b0 <| b1) <| b2) <| b3)
  )
  *)
let int32 : int32 Parser.t = 
  Parser.(
    int16 >>= fun lo ->
    int16 >>= fun hi ->
    return (Int32.of_int ((hi lsl 8) lor lo))
  )

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
  Parser.(
    ensure (byte >>= fun n -> guard (0 < n && n < 64)) >> byte >>= bytes
  )

let write_domain_name (name : domain_name) =
  let labels = split_domain name in
  Writer.(sequence write_label labels ++ byte 0)

let parse_domain_name : domain_name Parser.t =
  Parser.(
    let rec labels () =
      sequence parse_label       >>= fun ls  ->
      byte                       >>= fun n   ->
      if n = 0 then return ls else
        guard (n land 0xc0 = 0xc0) >>
          byte                   >>= fun m   ->
      let off = ((n land 0x3f) lsl 8) lor m in
      tell                       >>= fun pos ->
      seek off                   >>
        labels ()                >>= fun ls' ->
      seek pos                   >>
        return (ls @ ls')
    in fmap (String.concat ".") $ labels ()
  )
   
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
  Writer.(function
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
  )

let parse_resource rr_type rr_dlen =
  Parser.(match rr_type with
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
  )

type rsrc_record = {
  rr_name  : domain_name;
  rr_type  : rr_type;
  rr_class : rr_class;
  rr_ttl   : int32;
  rr_rdata : resource;
}

let write_rsrc_record r =
  Writer.(
    let rr_rdata = run (write_resource r.rr_rdata) in
    write_domain_name      r.rr_name
    ++ int16 (int_of_rr_type  r.rr_type)
    ++ int16 (int_of_rr_class r.rr_class)
    ++ int32                  r.rr_ttl
    ++ int16     (String.length rr_rdata)
    ++ bytes                    rr_rdata
  )

let parse_rsrc_record =
  Parser.(
    parse_domain_name              >>= fun rr_name  ->
    fmap rr_type_of_int  int16     >>= fun rr_type  ->
    fmap rr_class_of_int int16     >>= fun rr_class ->
    int32                          >>= fun rr_ttl   ->
    int16                          >>= fun rr_dlen  ->
    parse_resource rr_type rr_dlen >>= fun rr_rdata ->
    return { rr_name; rr_type; rr_class; rr_ttl; rr_rdata; }
  )

type question = {
  q_name  : domain_name;
  q_type  : q_type;
  q_class : q_class;
}
 
let write_question q =
  Writer.(
    write_domain_name     q.q_name
    ++ int16 (int_of_q_type  q.q_type )
    ++ int16 (int_of_q_class q.q_class)
  )

let parse_question =
  Parser.(
    parse_domain_name         >>= fun q_name  ->
    fmap q_type_of_int  int16 >>= fun q_type  ->
    fmap q_class_of_int int16 >>= fun q_class ->
    return { q_name; q_type; q_class; }
  )

type eaddr = string
type eth = {
  dmac: eaddr;
  smac: eaddr;
  etype: int16;
}

let parse_eth = 
  Parser.(
    bytes 6 >>= fun dmac ->
    bytes 6 >>= fun smac ->
    int16   >>= fun etype ->
    return { dmac; smac; etype }
  )    

type pcap = {
  ts_secs: int32;
  ts_usecs: int32;
  caplen: int32;
  pktlen: int32;
}

let parse_pcap = 
  Parser.(
    int32 >>= fun ts_secs ->
    int32 >>= fun ts_usecs ->
    int32 >>= fun caplen ->
    int32 >>= fun pktlen ->
    return { ts_secs; ts_usecs; caplen; pktlen }
  )

type pcap_file = {
  magic: int32;
  major: int16; 
  minor: int16;
  tzone: int32;
  snaplen: int32;
  linktype: int32;
}
let pcap_file_to_string pf =
  sp "(%08lx) %d.%d tzone:%ld snaplen:%ld linktype:%ld"
    pf.magic pf.major pf.minor pf.tzone pf.snaplen pf.linktype

let parse_pcap_file = 
  Parser.(
    int32 >>= fun magic ->
    int16 >>= fun major ->
    int16 >>= fun minor ->
    int32 >>= fun tzone ->
    int32 >>= fun _ ->
    int32 >>= fun snaplen ->
    int32 >>= fun linktype ->
    return { magic; major; minor; tzone; snaplen; linktype }
  )

type dns_record = {
  id         : int16;
  detail     : int16;
  question   : question    list;
  answer     : rsrc_record list;
  authority  : rsrc_record list;
  additional : rsrc_record list;
}

let write_dns_record d =
  Writer.(
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
  )

let parse_dns_record =
  Parser.(
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
  )

let query ?(q_type=`A) id q_name =
  if id land 0xffff <> id then invalid_arg "query" 
  else {
    id;
    detail     = 0b0_0000_0010_000_0000;
    question   = [ { q_name; q_type; q_class = `IN; } ];
    answer     = [];
    authority  = [];
    additional = []; 
  }

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
    match Parser.run parse_dns_record (String.sub buf 0 cnt) 0 with
      | Some dns, _ -> dns
      | None    , _ -> failwith "Parse error"
  ) sock

let mail_servers server domain =
  let res = query_dns server (query ~q_type:`MX 0 domain) in
  (List.sort (fun (p, _) (p', _) -> compare p p')
     (List.map (function
       | { rr_rdata = `Exchange (p, d); _ } -> (p, d)
       | _ -> failwith "query error")
        (List.filter (fun { rr_type; _ } -> rr_type = `MX)
           res.answer)))

let contents ic = (* from http://ocaml.tuxfamily.org/Reading_a_file *)
  let buf = Buffer.create 16384
  and tmp = String.create 4096 in
  let rec aux() =
    let bytes = input ic tmp 0 4096 in
    if bytes > 0 then begin
      Buffer.add_substring buf tmp 0 bytes;
      aux()
    end
  in
  (try aux() with End_of_file -> ());
  (Buffer.contents buf)

let pcap_to_string p = 
  Printf.sprintf "%ld.%06ld [%ld/%ld]" p.ts_secs p.ts_usecs p.caplen p.pktlen
let eaddr_to_string e = 
  sp "%02x-%02x-%02x-%02x-%02x-%02x" 
    (int_of_byte e.[0]) (int_of_byte e.[1]) (int_of_byte e.[2])
    (int_of_byte e.[3]) (int_of_byte e.[4]) (int_of_byte e.[5])

type packet =
| PCAP of pcap * packet
| ETH of eth * packet
| UNK of int
| EOF

let main_pcap () =
  let ic = open_in Sys.argv.(1) in
  unwind ~protect:close_in (fun ic ->
    let bs = contents ic in

    let hdr, (_,pkts) = Parser.run parse_pcap_file bs 0 in
    let hdr = (match hdr with
      | Some hdr 
        -> Printf.printf "%s\n" (pcap_file_to_string hdr); hdr
      | None -> failwith "not a pcap file"
    )
    in
    let rec loop i pos = 
      pr "!!! %d\n" pos;
      let h, (_,p) = Parser.run parse_pcap bs pos in
      let packet, caplen = (match h with
        | Some h 
          -> pr "[%d] %s\n" i (pcap_to_string h);
            PCAP(h,
                 match hdr.linktype with
                   | 0x00000001_l (* ethernet *)
                     -> let eh, (_,np) = Parser.run parse_eth bs p in
                        match eh with
                          | Some eh ->
                            Printf.printf "\t%s > %s [%04x]\n" 
                              (eaddr_to_string eh.smac)
                              (eaddr_to_string eh.dmac)
                              (eh.etype);
                            ETH(eh, UNK(np))
                          | None -> failwith "bad eth"
            ), h.caplen
        | None -> EOF, 0l
      )
      in loop (i+1) (pos+(Int32.to_int caplen)+16 (* pcap hdr size *))
    in
    loop 0 pkts
  ) ic

    (*
      match eh.etype with
      | 0x0800 (* ipv4 *)
      -> let ih, np = Parser.run parse_ipv4
    *)

(*
let main_dns_direct () = 

  (*** construct a dns response fragment
       let server, domain = "128.243.98.2", "google.com." in
       
       let d = query_dns server (query ~q_type:`A 0 domain) in
       let bs = Writer.run (write_dns_record d) in
       let oc = open_out "dns.out" in
       output_string oc bs; close_out oc
  *)
  
  let ic = open_in "dns.2.dat" in
  unwind ~protect:close_in (fun ic ->
    let ds = contents ic in
    let p = Parser.run in
    (match p parse_dns_record ds with
      | Some r -> print_endline "some"
      | None -> print_endline "none"
    )
  ) ic
*)

let _ = main_pcap ()

(* Parser.run evaluates the thunk it's passed in arg1 with the 
   cursor = (string * position) it's passed in arg2 *)

(* we will evaluate the first to get the pcap file; it should return
   not just the result (a pcap_file) but also the *remaining* bytes;
   we can then do the demux outside the monad -- since the demux
   occurs based on what we have, not what's coming -- and re-evaluate
   Parser.run passing in parse_pcap and remaining bytes.  that will
   give a pcap plus remaining bytes; again, demux (linktype=1 =>
   ethernet), and pass parse_eth and remaning bytes to Parser.run *)

