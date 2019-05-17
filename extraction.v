Require TFTP_Core.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.

Extraction Blacklist String Int List Nat.

(* tak można wstawiać ocamlowy kod do aksjomatów *)
Extract Constant TFTP_Core.newline => "'\n'".
Extract Constant TFTP_Core.hello => "['a';'b';'c']".

Separate Extraction
         BinNat BinNums BinInt BinPos (* to jest potrzebne do camlcoq *)
         TFTP_Core.
