Require Import Ascii.
Require Import List.
Require Import String.
Require Import Program.
Require Import ZArith.

(** Unicode codepoint literal support, based on
    https://github.com/arthuraa/poleiro/blob/master/theories/ForceOption.v *)

Open Scope char_scope.
Open Scope Z_scope.

Fixpoint _parse_hex_digit c :=
  match c with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | "A" | "a" => Some 10
  | "B" | "b" => Some 11
  | "C" | "c" => Some 12
  | "D" | "d" => Some 13
  | "E" | "e" => Some 14
  | "F" | "f" => Some 15
  | _ => None
  end.

Open Scope string_scope.

Fixpoint _parse_hex_opt_aux s accum :=
  match s with
  | "" => Some accum
  | String c s' => 
      match _parse_hex_digit c with
      | Some n => _parse_hex_opt_aux s' (16 * accum + n)
      | None => None
      end
  end.

Definition _parse_hex_opt s := _parse_hex_opt_aux s 0.

Lemma _parse_hex_opt_1: _parse_hex_opt "FFfE" = Some 65534.
Proof.
  auto.
Qed.

Lemma _parse_hex_opt_2: _parse_hex_opt "AAfg" = None.
Proof.
  auto.
Qed.

Inductive hexParseError := HexParseError.

Definition force_some {A} {ErrType} (o:option A) (e:ErrType) :
  match o with
  | Some _ => A
  | None => ErrType
  end
:=
  match o with
  | Some a => a
  | None => e
  end.

Definition parse_hex (s:string) := force_some (_parse_hex_opt s) HexParseError.

Lemma parse_hex_1: (parse_hex "FFfE" - 65534 = 0).
Proof.
  auto.
Qed.

Lemma parse_hex_2: parse_hex "AAfg" = HexParseError.
Proof.
  auto.
Qed.

Notation "U+ s" := (parse_hex s) (at level 0, no associativity).

Lemma U_1: U+"FfFe" = 65534.
Proof.
  auto.
Qed.

Lemma U_2: U+"AAfg" = HexParseError.
Proof.
  auto.
Qed.

Lemma U_3: U+"FfFe" + U+"0002" = 65536.
Proof.
  auto.
Qed.

Lemma U_4: Z.land U+"AA" U+"F0" = U+"A0".
Proof.
  auto.
Qed.

(** UTF-8 description based on https://tools.ietf.org/html/rfc3629#section-3 **)

(** UTF-8 decoding support **)

Definition _get_lo_bits c n :=
  Z.land (Z.of_N (N_of_ascii c)) ((Z.shiftl 1 n) - 1).

Definition _read_head_byte c :=
  match c with
  | Ascii _ _ _ _ _ _ _ false => Some ((_get_lo_bits c 7), 0%nat) 
  | Ascii _ _ _ _ _ false true true => Some ((_get_lo_bits c 5), 1%nat)
  | Ascii _ _ _ _ false true true true => Some ((_get_lo_bits c 4), 2%nat)
  | Ascii _ _ _ false true true true true => Some ((_get_lo_bits c 3), 3%nat)
  | _ => None
  end.

Fixpoint _decode_codepoint (acc:Z) (s:string) (n:nat) :=
  match n with
  | O => Some (acc, s)
  | S m =>
      match s with
      | String c s' =>
          match c with
          | Ascii _ _ _ _ _ _ false true =>
              _decode_codepoint ((Z.shiftl acc 6) + (_get_lo_bits c 6)) s' m
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint _utf8_decode_aux s dummy :=
  match s, dummy with
  | "", _ => Some nil
  | String c s', S m =>
      match _read_head_byte c with
      | Some (acc, n) =>
          match _decode_codepoint acc s' n with
          | Some (acc, s'') =>
              match _utf8_decode_aux s'' m with
              | Some l => Some (acc :: l)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _, _ => None
  end.

Definition utf8_decode (s:string): option (list Z) :=
  _utf8_decode_aux s (length s).

Definition _aux_enc_cp_byte cp hi lo :=
  ascii_of_N (Z.to_N (128 + Z.land (Z.shiftr cp lo) ((Z.shiftl 1 (hi - lo + 1)) - 1))).

Definition _encode_codepoint cp :=
  match (Z_le_dec cp U+"7F"), (Z_le_dec cp U+"7FF"), (Z_le_dec cp U+"FFFF"),
        (Z_le_dec cp U+"10FFFF") with
  | left _, _, _, _ =>
      Some (String (ascii_of_N (Z.to_N cp)) "")
  | _, left _, _, _ =>
      Some (String (_aux_enc_cp_byte cp 10 6) 
           (String (_aux_enc_cp_byte cp 5 0) ""))
  | _, _, left _, _ =>
      Some (String (_aux_enc_cp_byte cp 15 12)
           (String (_aux_enc_cp_byte cp 11 6)
           (String (_aux_enc_cp_byte cp 5 0) "")))
  | _, _, _, left _ =>
      Some (String (_aux_enc_cp_byte cp 20 18)
           (String (_aux_enc_cp_byte cp 17 12)
           (String (_aux_enc_cp_byte cp 11 6)
           (String (_aux_enc_cp_byte cp 5 0) ""))))
  | _, _, _, _ => None
  end.

Fixpoint utf8_encode (l:list Z) :=
  match l with
  | nil => Some ""
  | cp :: l' =>
      match _encode_codepoint cp, utf8_encode l' with
      | Some s, Some s' => Some (s ++ s')
      | _, _ => None
      end
  end.