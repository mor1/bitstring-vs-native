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
let sp = Printf.sprintf
let pr = Printf.printf
let ep = Printf.eprintf

exception Unparsable of string * bitstring

let (|>) x f = f x
let (>>) f g x = g (f x)
let (||>) l f = List.map f l

let (&&&) x y = x land y
let (|||) x y = x lor y
let (^^^) x y = x lxor y
let (<<<) x y = x lsl y
let (>>>) x y = x lsr y

let join c l = List.fold_left (fun x y -> y ^ c ^ x) "" l
let stop (x, bits) = x

type int8 = int
type int16 = int
type byte = char
let byte (i:int) : char = Char.chr i
let int_of_byte b = Char.code b

type bytes = string
let bytes_to_hex_string bs = 
  bs |> Array.map (fun b -> sp "%02x." (int_of_byte b))
let bytes_of_bitstring bits = string_of_bitstring bits

let ipv4_addr_to_string = Unix.string_of_inet_addr
let ipv4_addr_of_bytes = Obj.magic
let ipv4_addr_of_int32 = Obj.magic

type label = 
  | L of string * int
  | P of int
  | Z
            
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
  sp "%c:%02x %s:%s:%s:%s %02x %d"
    (if d.qr then 'R' else 'Q')
    (int_of_byte d.opcode)
    (if d.aa then "auth" else "non-auth")
    (if d.tc then "trunc" else "complete")
    (if d.rd then "recurse" else "non-rec")
    (if d.ra then "can-recurse" else "no-recurse")
    (int_of_byte d.z) (int_of_byte d.rcode)
               
type dns = {
  id          : int16;
  detail      : detail;
  questions   : question list;
  answers     : rsrc_record list;
  authorities : rsrc_record list;
  additionals : rsrc_record list;
}

let parse_charstr bits = 
  bitmatch bits with
    | { len: 8; str: (len*8): string; bits: -1: bitstring }
      -> str, bits

let parse_label base bits = 
  bitmatch bits with
    | { length: 8: check(length != 0 && length < 64), save_offset_to(ptr); 
        name: (length*8): string; data: -1: bitstring } 
      -> let offset = (ptr-base)/8 in
         pr "!!! ptr:%d base:%d offset:%d\n" ptr base offset;
         (L (name, offset), data)
    | { 0b0_11: 2; offset: 14; bits: -1: bitstring } 
      -> (P offset, bits)
    | { 0: 8; bits: -1: bitstring } -> (Z, bits)
    | { _ } -> raise(Unparsable ("parse_label", bits))

let parse_name base bits = 
  let names = Hashtbl.create 8 in
  
  let rec aux name bits = 
    match parse_label base bits with
      | (L (n, o), data) 
        -> Hashtbl.add names o n;
          aux (n :: name) data 
      | (P o, data) 
        -> let n = Hashtbl.find names o in
           (n :: name, data)
      | (Z, data)   
        -> (name, data)
  in 
  let name, bits = aux [] bits in
  (join "." name, bits)

let parse_resource base t bits = 
  match t with
    | `HINFO -> let (cpu, bits) = parse_charstr bits in
                let os = bits |> parse_charstr |> stop in
                `Hostinfo (cpu, os)
    | `MB | `MD | `MF | `MG | `MR | `NS
    | `CNAME | `PTR -> `Domain (bits |> parse_name base |> stop)
    | `MINFO -> let (rm, bits) = parse_name base bits in
                let em = bits |> parse_name base |> stop in
                `Mailbox (rm, em)
    | `MX -> (bitmatch bits with
        | { preference: 16; bits: -1: bitstring } 
          -> `Exchange (preference, bits |> parse_name base |> stop)
    )
    | `NULL -> `Data (string_of_bitstring bits)    
    | `TXT -> let names, _ = 
                let rec aux ns bits = 
                  let n, bits = parse_name base bits in
                  aux (n :: ns) bits
                in
                aux [] bits
              in
              `Text names
    | `SOA -> let mn, bits = parse_name base bits in
              let rn, bits = parse_name base bits in 
              (bitmatch bits with
                | { serial: 32; refresh: 32; retry: 32; expire: 32;
                    minimum: 32 }
                  -> `Authority (mn, rn, 
                                 serial, refresh, retry, expire, minimum)
              )
    | `A -> `Address (bits |> bytes_of_bitstring |> ipv4_addr_of_bytes)
    | `WKS -> (bitmatch bits with
        | { addr: 32; proto: 8; bitmap: -1: string } 
          -> `Services (addr |> ipv4_addr_of_int32, proto |> byte, bitmap)
    )
let string_of_resource r = 
  match r with
    | `Hostinfo (cpu, os) -> sp "Hostinfo (%s, %s)" cpu os
    | `Domain n -> sp "Domain (%s)" n
    | `Mailbox (rn, mn) -> sp "Mailbox (%s, %s)" rn mn
    | `Exchange (i, n) -> sp "Exchange (%d, %s)" i n
    | `Data d -> sp "Data (%s)" d
    | `Text ns -> sp "Text (%s)" (ns |> join "|")
    | `Authority (mn, rn, serial, refresh, retry, expire, min) 
      -> (sp "Authority (%s, %s, %ld,%ld,%ld,%ld,%ld)" 
            mn rn serial refresh retry expire min)
    | `Address a -> sp "Address (%s)" (ipv4_addr_to_string a)
    | `Services (a, p, bm) 
      -> (sp "Services (%s, %d, %s)"
            (Unix.string_of_inet_addr a) (int_of_byte p) bm)
      
let parse_question base bits = 
  let n, bits = parse_name base bits in
  bitmatch bits with
    | { t: 16; c: 16; data: -1: bitstring }
      -> { q_name = n;
           q_type = q_type_of_int t;
           q_class = q_class_of_int c;
         }, data
    | { _ } -> raise (Unparsable ("parse_question", bits))

let question_to_string q = 
  sp "%s <%s|%s>" 
    q.q_name (string_of_q_type q.q_type) (string_of_q_class q.q_class)
                                                         
let parse_rr base bits =
  let name, bits = parse_name base bits in
  bitmatch bits with
    | { t: 16; c: 16; ttl: 32; 
        rdlen: 16; rdata: (rdlen*8): bitstring;
        data: -1: bitstring } 
      -> { rr_name = name;
           rr_type = rr_type_of_int t;
           rr_class = rr_class_of_int c;
           rr_ttl = ttl;
           rr_rdata = parse_resource base (rr_type_of_int t) rdata;
         }, data
    | { _ } -> raise (Unparsable ("parse_rr", bits))
                                                        
let rr_to_string rr = 
  sp "%s <%s|%s|%ld> %s" 
    rr.rr_name 
    (string_of_rr_type rr.rr_type) (string_of_rr_class rr.rr_class) rr.rr_ttl
    (string_of_resource rr.rr_rdata)

let dns_to_string d = 
  sp "%04x %s <qs:%s> <an:%s> <au:%s> <ad:%s>"
    d.id (detail_to_string d.detail) 
    (d.questions ||> question_to_string |> join ",")
    (d.answers ||> rr_to_string |> join ",")
    (d.authorities ||> rr_to_string |> join ",")
    (d.additionals ||> rr_to_string |> join ",")


let parsen pf b n bits = 
  let rec aux rs n bits = 
    match n with
      | 0 -> rs, bits
      | _ -> let r, bits = pf b bits in 
             aux (r :: rs) (n-1) bits
  in
  aux [] n bits
    
let parse_dns bits = 
  let (_, base, _) = bits in
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
      let questions, bits = parsen parse_question base qdcount bits in
      let answers, bits = parsen parse_rr base ancount bits in
      let authorities, bits = parsen parse_rr base nscount bits in
      let additionals, bits = parsen parse_rr base arcount bits in
      { id = id; 
        detail = detail;
        questions = questions;
        answers = answers;
        authorities = authorities;
        additionals = additionals;
      }

    | { _ } -> raise (Unparsable ("parse_dns", bits))

type ipv4_flags = {
  df: bool;
  mf: bool;
}
let ipv4_flags_to_string fs = 
  sp "%s:%s" (if fs.df then "DF" else ".") (if fs.mf then "MF" else ".")

let parse_flags b = 
  { df = (b &&& 0b0_010) != 0;
    mf = (b &&& 0b0_001) != 0;
  }

type ipv4_option = [
| `NOP
| `Security of bytes
| `LooseSR of int * bytes
| `StrictSR of int * bytes
| `RecordR of int * bytes
| `StreamID of int32
(* | `Timestamp*) 
]  
   
let parse_options bits = 
  let rec aux os bits = 
    bitmatch bits with
      | { 0: 8 } -> os
      | { 1: 8 } -> aux (`NOP :: os) bits
      | { 130: 8; len: 8: check(len == 11*8) ; data: len: string } 
        -> aux (`Security data :: os) bits
      | { 131: 8; len: 8; ptr: 8; route: (len-3)*8: string }
        -> aux (`LooseSR (ptr, route) :: os) bits
      | { 137: 8; len: 8; ptr: 8; route: (len-3)*8: string }
        -> aux (`StrictSR (ptr, route) :: os) bits
      | { 7: 8; len: 8; ptr: 8; route: (len-3)*8: string }
        -> aux (`RecordR (ptr, route) :: os) bits
      | { 136: 8; 4: 8; streamid: 32 }
        -> aux (`StreamID streamid :: os) bits
      | { _ } -> raise (Unparsable ("parse_options", bits))
  in
(* aux [] bits *)
  []
          
type ipv4 = {
  version: int;
  hdrlen: int;
  tos: byte;
  length: int16;
  ident: int16;
  flags: ipv4_flags;
  offset: int;
  ttl: int8;
  proto: int8;
  cksum: int16;
  saddr: Unix.inet_addr;
  daddr: Unix.inet_addr;
  options: ipv4_option list;
}
let ipv4_to_string ih = 
  sp "%s > %s, (%d) [%d,%s,%s]"
    (ipv4_addr_to_string ih.saddr)
    (ipv4_addr_to_string ih.daddr)
    ih.proto ih.length
    (ih.flags |> ipv4_flags_to_string)
    ("") (* ih.options |> bytes_to_hex_string) *)

let parse_ipv4 bits = 
  bitmatch bits with
  | { version: 4; hdrlen: 4; tos: 8; length: 16;
      ident: 16; flags: 3; offset: 13;
      ttl: 8; proto: 8; cksum: 16;
      source: 32; dest: 32;
      options: (hdrlen-5)*32: bitstring;
      bits: -1: bitstring 
    } when version = 4 
      -> { version = version; hdrlen = hdrlen; tos = byte tos; length = length;
           ident = ident; flags = parse_flags flags; offset = offset;
           ttl = ttl; proto = proto; cksum = cksum;
           saddr = source |> ipv4_addr_of_int32;
           daddr = dest |> ipv4_addr_of_int32;
           options = parse_options options;
         }, bits
  | { _ } -> raise (Unparsable ("parse_ipv4", bits))

type eaddr = string
type eth = {
  dmac: eaddr;
  smac: eaddr;
  etype: int16;
}
let eaddr_to_string e = 
  sp "%02x-%02x-%02x-%02x-%02x-%02x" 
    (int_of_byte e.[0]) (int_of_byte e.[1]) (int_of_byte e.[2])
    (int_of_byte e.[3]) (int_of_byte e.[4]) (int_of_byte e.[5])

let parse_eth bits = 
  bitmatch bits with
    | { dmac: 48: string; smac: 48: string; etype: 16; 
        bits: -1: bitstring }
      -> { dmac=dmac; smac=smac; etype=etype; }, bits
let eth_to_string h = 
  sp "%s > %s [%04x]" (eaddr_to_string h.smac) (eaddr_to_string h.dmac) h.etype
  
type udp = {
  sport: int16;
  dport: int16;
  length: int16;
  cksum: int16;
}
let udp_to_string u = 
  sp "%d,%d" u.sport u.dport

let parse_udp bits = 
  bitmatch bits with
    | { sport: 16; dport: 16; length: 16; cksum: 16; bits: -1: bitstring }
      -> { sport = sport; dport = dport; 
           length = length; cksum = cksum;
         }, bits
    | { _ } -> raise (Unparsable ("parse_udp", bits))

type pcap = {
  ts_secs: int32;
  ts_usecs: int32;
  caplen: int32;
  pktlen: int32;
  pkt: bitstring;                
}
let parse_pcap e bits = 
  bitmatch bits with
    | { ts_secs: 32: endian (e);
        ts_usecs: 32: endian (e);
        caplen: 32: endian (e);
        pktlen: 32: endian (e);
        pkt: (Int32.to_int caplen*8): bitstring;
        bits: -1: bitstring
      }
      -> { ts_secs = ts_secs; ts_usecs = ts_usecs;
           caplen = caplen; pktlen = pktlen; 
           pkt = pkt;
         }, bits        

    | { _ } -> raise (Unparsable ("parse_pcap", bits))
let pcap_to_string p = 
  sp "%ld.%06ld [%ld/%ld]" p.ts_secs p.ts_usecs p.caplen p.pktlen

type packet =
| PCAP of pcap * packet
| ETH of eth * packet
| IPv4 of ipv4 * packet
| UDP of udp * packet
| DNS of dns

let is_wellknown_port p  = ((    0 <= p) && (p <=  1023))
let is_registered_port p = (( 1024 <= p) && (p <= 49151))
let is_ephemeral_port p  = ((49152 <= p) && (p <= 65535)) 
let svc_port p q = 
  match p,q with
    | p,_ when p |> is_wellknown_port -> p
    | _,q when q |> is_wellknown_port -> q
    
    | p,_ when p |> is_registered_port -> p
    | _,q when q |> is_registered_port -> q

    | _ -> min p q (* just default to the minimum *)
      
let port_dns = 53
let udp_demux bits = 
  let uh, bits = parse_udp bits in 
  UDP (uh, (match svc_port uh.sport uh.dport with
    | port_dns -> DNS (parse_dns bits)
  ))

let proto_icmp =   1
let proto_tcp  =   6
let proto_udp  =  17
let ipv4_demux bits = 
  let ih, bits = parse_ipv4 bits in 
  IPv4(ih, bits |> (match ih.proto with
    | proto_udp -> udp_demux
  ))

let packet_to_string pkt = 
  let rec aux p sep str = 
    match p with
      | PCAP (h, d) -> let str = sp "%sPCAP(%s)%s" str (pcap_to_string h) sep in
                       aux d sep str  
      | ETH (h, d) -> let str = sp "%sETH(%s)%s" str (eth_to_string h) sep in
                      aux d sep str
      | IPv4 (h, d) -> let str = sp "%sIPv4(%s)%s" str (ipv4_to_string h) sep in
                       aux d sep str
      | UDP (h, d) -> let str = sp "%sUDP(%s)%s" str (udp_to_string h) sep in
                      aux d sep str

      | DNS d -> sp "%sDNS(%s)" str (dns_to_string d)
  in
  aux pkt "\n\t|" ""
    
let etype_ipv4 = 0x0800
let etype_arp  = 0x0806
let etype_ipx  = 0x8137
let etype_ipv6 = 0x86dd
let eth_demux bits = 
  let eh, bits = parse_eth bits in
  ETH(eh, bits |> (match eh.etype with
    | etype_ipv4 -> ipv4_demux
  ))
let pcap_demux e bits = 
  let ph, bits = parse_pcap e bits in
  PCAP (ph, ph.pkt |> eth_demux), bits
                         
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
                                                              
let magic_le = 0x0_d4c3b2a1_l
and magic_be = 0x0_a1b2c3d4_l
and endian_of = function
  | 0x0_d4c3b2a1_l -> Bitstring.LittleEndian
  | 0x0_a1b2c3d4_l -> Bitstring.BigEndian
  | _ -> assert false
                                            
let parse_pcap_file bits = 
  bitmatch bits with
    | { ((0x0_d4c3b2a1_l|0x0_a1b2c3d4_l) as magic): 32;
        major: 16: endian (endian_of magic);
        minor: 16: endian (endian_of magic);
        tzone: 32: endian (endian_of magic);
        _: 32;
        snaplen: 32: endian (endian_of magic);
        linktype: 32: endian (endian_of magic);
        bits: -1: bitstring
      }
      -> { magic = magic;
           major = major; minor = minor;
           tzone = tzone;
           snaplen = snaplen;
           linktype = linktype;
         }, bits        

let main_dns_direct () = 
  let fn = "dns.dat" in
  let bits = bitstring_of_file fn in
  try
    let dns = parse_dns bits in
    pr "id:%04x detail:%s\n" dns.id (detail_to_string dns.detail);
    pr "qds: %s\n" 
      (dns.questions ||> question_to_string |> join "\n\t");
    pr "ans: %s\n" 
      (dns.answers ||> rr_to_string |> join "\n\t");
    pr "nss: %s\n" 
      (dns.authorities ||> rr_to_string |> join "\n\t");
    pr "ars: %s\n" 
      (dns.additionals ||> rr_to_string |> join "\n\t")
  with
      Unparsable (where, what) ->
        pr "EXC: %s\n" where;
        hexdump_bitstring stdout what

let main_pcap () = 
  let fn = "test.pcap" in
  let bits = bitstring_of_file fn in
  try
    let hdr, pkts = parse_pcap_file bits in
    pr "PCAP FILE: %s\n" (pcap_file_to_string hdr);

    let rec aux e i bits = 
      if bitstring_length bits != 0 then
        let p, bits = pcap_demux e bits in
        let _, offset, length = bits in
        pr "!!! %d %d\n" offset length;
        pr "%d: %s\n" i (p |> packet_to_string);
        aux e (i+1) bits
    in
    let e = endian_of hdr.magic in
    aux e 0 pkts

  with
      Unparsable (where, what) ->
        ep "EXC: %s\n" where;
        hexdump_bitstring stdout what

let _ = main_dns_direct ()
let _ = main_pcap ()
