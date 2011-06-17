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

open Bitstring

exception Unparsable of string * bitstring

let (|>) x f = f x
let (>>) f g x = g (f x)
let (||>) l f = List.map f l
let join c l = List.fold_left (fun x y -> y ^ c ^ x) "" l
let stop (x, bits) = x

type int16 = int
type byte = char
let byte (i:int) : char = Char.chr i
let int_of_byte b = Char.code b

type bytes = string
type label = string
type domain_name = string
let string o = match o with | Some x -> x | None -> ""

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
and string_of_rr_type:rr_type -> string = function
  | `A     ->  "A"
  | `NS    ->  "NS"
  | `MD    ->  "MD"
  | `MF    ->  "MF"
  | `CNAME ->  "CNAME"
  | `SOA   ->  "SOA"
  | `MB    ->  "MB"
  | `MG    ->  "MG"
  | `MR    ->  "MR"
  | `NULL  -> "NULL"
  | `WKS   -> "WKS"
  | `PTR   -> "PTR"
  | `HINFO -> "HINFO"
  | `MINFO -> "MINFO"
  | `MX    -> "MX"
  | `TXT   -> "TXT"
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
and string_of_q_type:q_type -> string = function
  | `AXFR         -> "AXFR"
  | `MAILB        -> "MAILB"
  | `MAILA        -> "MAILA"
  | `ANY          -> "ANY"
  | #rr_type as t -> string_of_rr_type t
and q_type_of_int : int -> q_type = function
  | 252           -> `AXFR
  | 253           -> `MAILB
  | 254           -> `MAILA
  | 255           -> `ANY
  | n             -> (rr_type_of_int n :> q_type)

type rr_class = [ `INx (* why can this not be `IN??? *) 
                | `CS | `CH | `HS ]

type q_class = [ rr_class | `ANY ]

let int_of_rr_class : rr_class -> int = function
  | `INx -> 1
  | `CS -> 2
  | `CH -> 3
  | `HS -> 4
and string_of_rr_class : rr_class -> string = function
  | `INx -> "IN"
  | `CS -> "CS"
  | `CH -> "CH"
  | `HS -> "HS"
and rr_class_of_int : int -> rr_class = function
  | 1   -> `INx
  | 2   -> `CS
  | 3   -> `CH
  | 4   -> `HS
  | _   -> invalid_arg "rr_class_of_int"

let int_of_q_class : q_class -> int = function
  | `ANY           -> 255
  | #rr_class as c -> int_of_rr_class c
and string_of_q_class : q_class -> string = function
  | `ANY           -> "ANY"
  | #rr_class as c -> string_of_rr_class c
and q_class_of_int : int -> q_class = function
  | 255            -> `ANY
  | n              -> (rr_class_of_int n :> q_class)

type resource = [
| `Hostinfo  of string * string
| `Domain    of domain_name
| `Mailbox   of domain_name * domain_name
| `Exchange  of int * domain_name
| `Data      of bytes
| `Text      of string list
| `Authority of domain_name * domain_name * int32 * int32 * int32 * int32 * int32
| `Address   of Unix.inet_addr
| `Services  of Unix.inet_addr * byte * bytes
]

type rsrc_record = {
  rr_name  : domain_name;
  rr_type  : rr_type;
  rr_class : rr_class;
  rr_ttl   : int32;
  rr_rdata : resource;
}

type question = {
  q_name  : domain_name;
  q_type  : q_type;
  q_class : q_class;
}

type detail = {
  qr: bool; 
  opcode: byte;
  aa: bool; 
  tc: bool; 
  rd: bool; 
  ra: bool;
  z: byte;
  rcode: byte;  
}
let detail_to_string d = 
  Printf.sprintf "%c:%02x %s:%s:%s:%s %02x %d"
    (if d.qr then 'R' else 'Q')
    (int_of_byte d.opcode)
    (if d.aa then "auth" else "non-auth")
    (if d.tc then "trunc" else "complete")
    (if d.rd then "recurse" else "non-rec")
    (if d.ra then "can-recurse" else "no-recurse")
    (int_of_byte d.z) (int_of_byte d.rcode)
               
type dns_record = {
  id          : int16;
  detail      : detail;
  questions   : question list;
  answers     : rsrc_record list;
  authorities : rsrc_record list;
  additionals : rsrc_record list;
}

let parse_label bits = 
  bitmatch bits with
    | { length: 8: check(length != 0); name: (length*8): string; 
        data: -1: bitstring } 
      -> (Some name, data)
    | { 0: 8; bits: -1: bitstring } -> (None, bits)
    | { _ } -> raise(Unparsable ("parse_label", bits))

let parse_name bits = 
  let rec aux name bits = 
    match parse_label bits with
      | (Some n, data) -> aux (n :: name) data 
      | (None, data)   -> (name, data)
  in 
  let name, bits = aux [] bits in
  (join "." name, bits)

let parse_resource t bits = 
  match t with
    | `HINFO -> let (cpu, bits) = parse_label bits in
                let os = bits |> parse_label |> stop in
                `Hostinfo (string cpu, string os)
    | `MB | `MD | `MF | `MG | `MR | `NS
    | `CNAME | `PTR -> `Domain (bits |> parse_name |> stop)
    | `MINFO -> let (rm, bits) = parse_name bits in
                let em = bits |> parse_name |> stop in
                `Mailbox (rm, em)
    | `MX -> (bitmatch bits with
        | { preference: 16; bits: -1: bitstring } 
          -> `Exchange (preference, bits |> parse_name |> stop)
    )
    | `NULL -> `Data (string_of_bitstring bits)    
    | `TXT -> let names, _ = 
                let rec aux ns bits = 
                  let n, bits = parse_name bits in
                  Printf.printf "!!! %d\n" (bits |> bitstring_length);
                  aux (n :: ns) bits
                in
                aux [] bits
              in
              `Text names
    | `SOA -> let mn, bits = parse_name bits in
              let rn, bits = parse_name bits in 
              (bitmatch bits with
                | { serial: 32; refresh: 32; retry: 32; expire: 32;
                    minimum: 32 }
                  -> `Authority (mn, rn, 
                                 serial, refresh, retry, expire, minimum)
              )
    | `A -> `Address (bits |> string_of_bitstring |> Obj.magic)
    | `WKS -> (bitmatch bits with
        | { addr: 32; proto: 8; bitmap: -1: string } 
          -> `Services (addr |> Obj.magic, proto |> byte, bitmap)
    )
let string_of_resource r = 
  match r with
    | `Hostinfo (cpu, os) -> Printf.sprintf "Hostinfo (%s, %s)" cpu os
    | `Domain n -> Printf.sprintf "Domain (%s)" n
    | `Mailbox (rn, mn) -> Printf.sprintf "Mailbox (%s, %s)" rn mn
    | `Exchange (i, n) -> Printf.sprintf "Exchange (%d, %s)" i n
    | `Data d -> Printf.sprintf "Data (%s)" d
    | `Text ns -> Printf.sprintf "Text (%s)" (ns |> join "|")
    | `Authority (mn, rn, serial, refresh, retry, expire, min) 
      -> (Printf.sprintf "Authority (%s, %s, %d,%d,%d,%d,%d)" 
            mn rn (Int32.to_int serial) (Int32.to_int refresh)
            (Int32.to_int retry) (Int32.to_int expire) (Int32.to_int min))
    | `Address a -> Printf.sprintf "Address (%s)" (Unix.string_of_inet_addr a)
    | `Services (a, p, bm) 
      -> (Printf.sprintf "Services (%s, %d, %s)"
            (Unix.string_of_inet_addr a) (int_of_byte p) bm)
      
let parse_question bits = 
  let n, bits = parse_name bits in
  bitmatch bits with
    | { t: 16; c: 16; data: -1: bitstring }
      -> { q_name = n;
           q_type = q_type_of_int t;
           q_class = q_class_of_int c;
         }, data
    | { _ } -> raise (Unparsable ("parse_question", bits))

let question_to_string q = 
  Printf.sprintf "%s <%s|%s>" 
    q.q_name (string_of_q_type q.q_type) (string_of_q_class q.q_class)
                                                         
let parse_rr bits =
  let name, bits = parse_name bits in
  bitmatch bits with
    | { t: 16; c: 16; ttl: 32; 
        rdlen: 16; rdata: (rdlen*8): bitstring;
        data: -1: bitstring } 
      -> { rr_name = name;
           rr_type = rr_type_of_int t;
           rr_class = rr_class_of_int c;
           rr_ttl = ttl;
           rr_rdata = parse_resource (rr_type_of_int t) rdata;
         }, data
    | { _ } -> raise (Unparsable ("parse_rr", bits))
                                                        
let rr_to_string rr = 
  Printf.sprintf "%s <%s|%s|%s> %s" 
    rr.rr_name (string_of_rr_type rr.rr_type) 
    (string_of_rr_class rr.rr_class) (Int32.to_string rr.rr_ttl)
    (string_of_resource rr.rr_rdata)

let parsen pf n bits = 
  let rec aux rs n bits = 
    match n with
      | 0 -> rs, bits
      | _ -> let r, bits = pf bits in 
             aux (r :: rs) (n-1) bits
  in
  aux [] n bits
    
let parse_dns bits = 
  bitmatch bits with
    | { id: 16; 
        qr: 1; opcode: 4; aa: 1; tc: 1; rd: 1; ra: 1; z: 3; rcode: 4; 
        qdcount: 16; ancount: 16; nscount: 16; arcount: 16;
        bits: -1: bitstring
      } -> 
      let detail = { qr = qr; opcode = byte opcode;
                     aa = aa; tc = tc; rd = rd; ra = ra;
                     z = byte z; rcode = byte rcode } 
      in
      let questions, bits = parsen parse_question qdcount bits in
      let answers, bits = parsen parse_rr ancount bits in
      let authorities, bits = parsen parse_rr nscount bits in
      let additionals, bits = parsen parse_rr arcount bits in
      { id = id; 
        detail = detail;
        questions = questions;
        answers = answers;
        authorities = authorities;
        additionals = additionals;
      }

    | { _ } -> raise (Unparsable ("parse_dns", bits))

let _ = 
  let fn = "dns.dat" in
  let bits = Bitstring.bitstring_of_file fn in
  try
    let dns = parse_dns bits in
    Printf.printf "id:%04x detail:%s\n" dns.id (detail_to_string dns.detail);
    Printf.printf "qds: %s\n" 
      (dns.questions ||> question_to_string |> join "\n\t");
    Printf.printf "ans: %s\n" 
      (dns.answers ||> rr_to_string |> join "\n\t");
    Printf.printf "nss: %s\n" 
      (dns.authorities ||> rr_to_string |> join "\n\t");
    Printf.printf "ars: %s\n" 
      (dns.additionals ||> rr_to_string |> join "\n\t")
  with
      Unparsable (where, what) ->
        Printf.printf "EXC: %s\n" where;
        hexdump_bitstring stdout what
