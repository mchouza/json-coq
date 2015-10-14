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

Fixpoint _utf8_decode_aux (s:string) (acc:Z) (phase:nat): option (list Z) :=
  match s, acc, phase with
  (* base case *)
  | "", 0, O => Some []
  (* normal case, decides based on the first byte *)
  | String c s, 0, O =>
    match c with
    (* ASCII character, just decodes it *)
    | Ascii _ _ _ _ _ _ _ false =>
      match _utf8_decode_aux s 0 0 with
      | Some l => Some ((Z.of_N (N_of_ascii c)) :: l)
      | _ => None
      end
    (* FIXME: ADD HANDLING FOR CODEPOINTS WITH LONGER ENCODINGS *)
    | _ => None
    end
  (* FIXME: ADD HANDLING FOR THE OTHER PHASES *)
  | _, _, _ => None
  end.

Definition utf8_decode (s:string): option (list Z) :=
  _utf8_decode_aux s 0 0.


(** UTF-8 encoding support **)

Definition _aux_enc_cp_byte cp hi lo offset :=
  ascii_of_N (Z.to_N (Z.lor offset (Z.land (Z.shiftr cp lo) ((Z.shiftl 1 (hi - lo + 1)) - 1)))).

Definition _encode_codepoint cp :=
  match (Z_lt_dec cp 0), (Z_le_dec cp U+"7F"), (Z_le_dec cp U+"7FF"),
        (Z_le_dec cp U+"D7FF"), (Z_le_dec cp U+"DFFF"),
        (Z_le_dec cp U+"FFFF"), (Z_le_dec cp U+"10FFFF") with
  | left _, _, _, _, _, _, _ => None
  | _, left _, _, _, _, _, _ =>
      Some (String (ascii_of_N (Z.to_N cp)) "")
  | _, _, left _, _, _, _, _ =>
      Some (String (_aux_enc_cp_byte cp 10 6 U+"C0") 
           (String (_aux_enc_cp_byte cp 5 0 U+"80") ""))
  | _, _, _, left _, _, _, _ =>
      Some (String (_aux_enc_cp_byte cp 15 12 U+"E0")
           (String (_aux_enc_cp_byte cp 11 6 U+"80")
           (String (_aux_enc_cp_byte cp 5 0 U+"80") "")))
  | _, _, _, _, left _, _, _ => None
  | _, _, _, _, _, left _, _ =>
      Some (String (_aux_enc_cp_byte cp 15 12 U+"E0")
           (String (_aux_enc_cp_byte cp 11 6 U+"80")
           (String (_aux_enc_cp_byte cp 5 0 U+"80") "")))
  | _, _, _, _, _, _, left _ =>
      Some (String (_aux_enc_cp_byte cp 20 18 U+"F0")
           (String (_aux_enc_cp_byte cp 17 12 U+"80")
           (String (_aux_enc_cp_byte cp 11 6 U+"80")
           (String (_aux_enc_cp_byte cp 5 0 U+"80") ""))))
  | _, _, _, _, _, _, _ => None
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


(** Auxiliary theorems **)

(* FIXME: ADD REQUIRED THEOREMS *)


(** Unicode encoding/decoding theorems **)

Inductive is_valid_unicode: list Z -> Prop :=
  | ivu_empty: is_valid_unicode nil
  | ivu_cons: 
      forall c l, (0 <= c < U+"D800" \/ U+"DFFF" < c <= U+"10FFFF") ->
      is_valid_unicode l -> is_valid_unicode (c :: l).

Theorem valid_unicode_is_encoded:
  forall l, is_valid_unicode l <-> exists s, utf8_encode l = Some s.
Proof.
  assert (forall t:string, exists s, Some t = Some s) as ex_eq by (intros; exists t; auto).
  intros l; split.
  + induction l.
    - intros; exists ""; auto.
    - remember (a :: l) as a_l; intro ivu_a_l; destruct ivu_a_l as [|c l' c_bounds].
      * discriminate.
      * injection Heqa_l as a_eq l_eq; subst c; subst l'; clear Heqa_l.
        specialize (IHl ivu_a_l); clear ivu_a_l; destruct IHl as [s' l_enc_eq].
        unfold utf8_encode, _encode_codepoint in *.
        unfold "U+" in c_bounds; simpl in c_bounds.
        destruct (Z_lt_dec a 0); try omega.
        destruct (Z_le_dec a U+"7F"); try (rewrite l_enc_eq; apply ex_eq).
        destruct (Z_le_dec a U+"7FF"); try (rewrite l_enc_eq; apply ex_eq).
        destruct (Z_le_dec a U+"D7FF"); try (rewrite l_enc_eq; apply ex_eq).
        destruct (Z_le_dec a U+"DFFF"); try (unfold "U+" in *; simpl in *; omega).
        destruct (Z_le_dec a U+"FFFF"); try (rewrite l_enc_eq; apply ex_eq).
        destruct (Z_le_dec a U+"10FFFF"); try (rewrite l_enc_eq; apply ex_eq).
        unfold "U+" in *; simpl in *; omega.
  + induction l.
    - constructor.
    - simpl; remember (_encode_codepoint a) as a_enc.
      destruct (utf8_encode l), a_enc; intros [s' enc_eq]; try discriminate.
      specialize (IHl (ex_eq s)).
      constructor; try apply IHl.
      unfold _encode_codepoint in *.
      destruct (Z_lt_dec a 0); try discriminate.
      destruct (Z_le_dec a U+"7F"); try (unfold "U+" in *; simpl in *; omega).
      destruct (Z_le_dec a U+"7FF"); try (unfold "U+" in *; simpl in *; omega).
      destruct (Z_le_dec a U+"D7FF"); try (unfold "U+" in *; simpl in *; omega).
      destruct (Z_le_dec a U+"DFFF"); try discriminate.
      destruct (Z_le_dec a U+"FFFF"); try (unfold "U+" in *; simpl in *; omega).
      destruct (Z_le_dec a U+"10FFFF"); try (unfold "U+" in *; simpl in *; omega).
      discriminate.
Qed.

Theorem decoded_iff_encoded:
  forall l s, utf8_encode l = Some s <-> utf8_decode s = Some l.
Proof.
Admitted.