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

Fixpoint _utf8_decode_aux (s:string) (acc:Z) (phase:nat) (bound:Z): option (list Z) :=
  match s, acc, phase, bound with
  (* base case *)
  | "", 0, 0%nat, 0 => Some []
  (* normal case, decides based on the first byte *)
  | String c s, 0, 0%nat, 0 =>
    match c with
    (* ASCII character, just decodes it *)
    | Ascii _ _ _ _ _ _ _ false =>
      match _utf8_decode_aux s 0 0 0 with
      | Some l => Some ((Z.of_N (N_of_ascii c)) :: l)
      | _ => None
      end
    (* two bytes codepoint *)
    | Ascii _ _ _ _ _ false true true =>
      _utf8_decode_aux s (_get_lo_bits c 5) 1 U+"80"
    (* three bytes codepoint *)
    | Ascii _ _ _ _ false true true true =>
      _utf8_decode_aux s (_get_lo_bits c 4) 2 U+"800"
    (* four bytes codepoint *)
    | Ascii _ _ _ false true true true true =>
      _utf8_decode_aux s (_get_lo_bits c 3) 3 U+"10000"
    (* invalid *)
    | _ => None
    end
  (* final phase of multibyte codepoint *)
  | String c s, acc, 1%nat, bound =>
    (* checks c & the tail decoding *)
    match c, _utf8_decode_aux s 0 O 0 with
    | Ascii _ _ _ _ _ _ false true, Some l =>
      (* calculates the codepoint and checks it *)
      let cp := (Z.lor (Z.shiftl acc 6) (_get_lo_bits c 6)) in
      match (Z_ge_dec cp bound), (Z_le_dec cp U+"D7FF"), (Z_le_dec cp U+"DFFF") with
      | left _, left _, _ => Some (cp :: l)
      | left _, _, right _ => Some (cp :: l)
      | _, _, _ => None
      end
    | _, _ => None
    end
  (* intermediate phase of multibyte codepoint *)
  | String c s, acc, S n, bound =>
    (* checks c *)
    match c with
    | Ascii _ _ _ _ _ _ false true =>
      _utf8_decode_aux s (Z.lor (Z.shiftl acc 6) (_get_lo_bits c 6)) n bound
    | _ => None
    end
  (* invalid *)
  | _, _, _, _ => None
  end.

Definition utf8_decode (s:string): option (list Z) :=
  _utf8_decode_aux s 0 0 0.


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

Lemma land_bounds:
  forall a b,
  0 <= a ->
  0 <= b ->
  0 <= Z.land a b <= a.
Proof.
  intros a b a_bounds b_bounds.
  (* clears the easy cases first *)
  destruct a as [|p|p], b as [|q|q]; simpl; try omega;
  assert (Z.neg p < 0) as np_is_neg by apply Zlt_neg_0;
  assert (Z.neg q < 0) as nq_is_neg by apply Zlt_neg_0; try omega.
  clear a_bounds b_bounds np_is_neg nq_is_neg; generalize q; clear q.
  (* easy lemmas for positive values *)
  assert (forall p, 0 < Z.pos p) as pos_gt_0 by apply Pos2Z.is_pos.
  assert (forall p, 0 <= Z.pos p) as pos_ge_0 by (intros p'; specialize (pos_gt_0 p'); omega).
  assert (forall p, 1 <= Z.pos p) as pos_ge_1 by (intros p'; specialize (pos_gt_0 p'); omega).
  (* now the main induction, clearing the trivial cases first *)
  induction p; destruct q; try (split; discriminate);
  simpl; remember (Pos.land p q) as pnq; destruct pnq; simpl;
  specialize (IHp q); rewrite <-Heqpnq in IHp; simpl in IHp;
  unfold "<=", "?=", "?="%positive in *; simpl; auto.
  (* the final case *)
  rewrite Pos.compare_cont_spec in *; destruct (p0 ?= p)%positive; simpl; auto.
Qed.

Lemma lor_bounds:
  forall a b,
  0 <= a ->
  0 <= b ->
  a <= Z.lor a b <= a + b.
Proof.
  intros a b a_bound b_bound.
  (* clears the easy cases *)
  destruct a as [|p|p], b as [|q|q]; simpl; try omega;
  assert (Z.neg p < 0) as np_is_neg by apply Zlt_neg_0;
  assert (Z.neg q < 0) as nq_is_neg by apply Zlt_neg_0; try omega.
  clear a_bound b_bound np_is_neg nq_is_neg; generalize q; clear q.
  (* comparison lemmas *)
  assert (forall c, Pos.switch_Eq Eq c = c) as switch_eq_eq by
    (destruct c; auto).
  assert (forall p' c, Pos.compare_cont p' p' c = c) as p_p_keeps by
    (induction p'; simpl; auto).
  assert (forall p' c, Pos.compare_cont p' (Pos.succ p') c = Lt) as p_lt_succ by
    (induction p'; simpl; auto).
  (* now the main induction *)
  induction p; destruct q; simpl; try specialize IHp with (q := q);
  (* cleans up the easy cases *)
  try apply IHp; try omega;
  unfold "<=", "?=", "?="%positive in *; simpl; 
  repeat rewrite p_p_keeps; repeat rewrite p_lt_succ; 
  try (split; discriminate); split; try apply IHp.
  (* now the two hardest inequalities remain *)
  + repeat rewrite Pos.add_carry_spec in *; repeat rewrite Pos.compare_cont_spec in *;
    repeat rewrite Pos.compare_succ_r in *.
    remember (Pos.lor p q ?= p + q)%positive as c.
    repeat rewrite switch_eq_eq in *; destruct c; simpl; try discriminate.
    apply IHp.
  + repeat rewrite Pos.compare_cont_spec in *.
    remember (p ?= Pos.lor p q)%positive as c.
    repeat rewrite switch_eq_eq in *; destruct c; simpl; try discriminate.
    apply IHp.
Qed.

Lemma lor_acc_lo_bits_bounds:
  forall acc acc_lo acc_hi a n,
  0 <= acc_lo ->
  acc_lo <= acc_hi ->
  acc_lo <= acc <= acc_hi ->
  0 <= n < 8 ->
  Z.shiftl acc_lo n <=
  Z.lor (Z.shiftl acc n) (_get_lo_bits a n) <
  (Z.shiftl acc_hi n) + (Z.shiftl 1 n).
Proof.
  (* intros *)
  intros acc acc_lo acc_hi a n.
  intros acc_lo_bound acc_hi_bounds acc_bounds n_bounds.
  (* bounds _get_lo_bits *)
  assert (0 <= _get_lo_bits a n <= Z.shiftl 1 n - 1) as get_lo_bits_bounds.
  {
    unfold _get_lo_bits.
    rewrite Z.land_comm.
    apply land_bounds.
    + rewrite Z.shiftl_1_l.
      cut (0 < 2 ^ n). omega.
      apply Z.pow_pos_nonneg; omega.
    + apply N2Z.is_nonneg.
  }
  (* bounds the logical OR *)
  assert (Z.shiftl acc n <=
          Z.lor (Z.shiftl acc n) (_get_lo_bits a n) <=
          Z.shiftl acc n + _get_lo_bits a n) as acc_lor_lo_bounds.
  {
    apply lor_bounds.
    + rewrite Z.shiftl_mul_pow2, <-Zmult_0_r with (n := 0) by omega.
      apply Zmult_le_compat; try omega.
      apply Z.pow_nonneg; omega.
    + omega.
  }
  (* bounds the shifted accumulator *)
  assert (0 <= 2^n) as two_to_n_nonneg by (apply Z.pow_nonneg; omega).
  assert (Z.shiftl acc_lo n <= Z.shiftl acc n <= Z.shiftl acc_hi n) as shifted_acc_bounds.
  {
    repeat rewrite Z.shiftl_mul_pow2 by omega.
    split; apply Zmult_le_compat; omega.
  }
  (* finally omega has all the info it needs *)
  omega.
Qed.


(** Unicode encoding/decoding theorems **)

Inductive is_valid_unicode: list Z -> Prop :=
  | ivu_empty: is_valid_unicode nil
  | ivu_cons: 
      forall c l, (0 <= c < U+"D800" \/ U+"DFFF" < c <= U+"10FFFF") ->
      is_valid_unicode l -> is_valid_unicode (c :: l).

Lemma valid_cp_is_encoded:
  forall a, (0 <= a < U+"D800" \/ U+"DFFF" < a <= U+"10FFFF") <->
  exists s, _encode_codepoint a = Some s.
Proof.
  assert (forall t:string, exists s, Some t = Some s) as ex_eq by (intros; exists t; auto).
  Ltac oor_tactic := unfold "U+" in *; simpl in *; split; [intros; omega | intros [s Habs]; discriminate].
  Ltac ir_tactic := unfold "U+" in *; simpl in *; split; [intros | intros; omega].
  intros a; unfold _encode_codepoint.
  destruct (Z_lt_dec a 0). oor_tactic.
  destruct (Z_le_dec a U+"7F"). ir_tactic; apply ex_eq.
  destruct (Z_le_dec a U+"7FF"). ir_tactic; apply ex_eq.
  destruct (Z_le_dec a U+"D7FF"). ir_tactic; apply ex_eq.
  destruct (Z_le_dec a U+"DFFF"). oor_tactic.
  destruct (Z_le_dec a U+"FFFF"). ir_tactic; apply ex_eq.
  destruct (Z_le_dec a U+"10FFFF"). ir_tactic; apply ex_eq.
  oor_tactic.
Qed.

Theorem valid_unicode_is_encoded:
  forall l, is_valid_unicode l <-> exists s, utf8_encode l = Some s.
Proof.
  induction l.
  + simpl; split; intros; [exists ""; auto | apply ivu_empty].
  + unfold utf8_encode; fold utf8_encode; split.
    - intros ivu_a_l; inversion ivu_a_l as [|a' l' a_bounds ivu_l].
      rewrite IHl in ivu_l; destruct ivu_l as [s' l_enc_eq].
      rewrite valid_cp_is_encoded in a_bounds; destruct a_bounds as [s'' a_enc_eq].
      rewrite l_enc_eq, a_enc_eq; exists (s'' ++ s'); auto.
    - remember (_encode_codepoint a) as ecp_a.
      destruct ecp_a, (utf8_encode l); try (intros [s' Habs]; discriminate).
      intros _; apply ivu_cons.
      * rewrite valid_cp_is_encoded, <-Heqecp_a; exists s; auto.
      * rewrite IHl; exists s0; auto.
Qed.

Lemma aux_decode_higher_phase_non_empty:
  forall s acc n bound,
  _utf8_decode_aux s acc (S n) bound <> Some [].
Proof.
  intros s acc n bound.
  generalize s acc; clear s acc.
  induction n.
  + destruct s.
    - intros; case acc; discriminate.
    - unfold _utf8_decode_aux; fold _utf8_decode_aux; intros.
      remember (Z.lor (Z.shiftl acc 6) (_get_lo_bits a 6)) as cp.
      destruct (_utf8_decode_aux s 0 0 0), (Z_ge_dec cp bound),
               (Z_le_dec cp U+("D7FF")), (Z_le_dec cp U+("DFFF")),
               acc, a;
      destruct b5, b6; discriminate.
  + destruct s.
    - intros; case acc; discriminate.
    - unfold _utf8_decode_aux; fold _utf8_decode_aux; intros.
      destruct acc, a; destruct b5, b6; try discriminate; apply IHn.
Qed.

Lemma encode_codepoint_non_empty:
  forall cp, _encode_codepoint cp <> Some "".
Proof.
  intros; unfold _encode_codepoint.
  destruct (Z_lt_dec cp 0). discriminate.
  destruct (Z_le_dec cp U+"7F"). discriminate.
  destruct (Z_le_dec cp U+"7FF"). discriminate.
  destruct (Z_le_dec cp U+"D7FF"). discriminate.
  destruct (Z_le_dec cp U+"DFFF"). discriminate.
  destruct (Z_le_dec cp U+"FFFF"). discriminate.
  destruct (Z_le_dec cp U+"10FFFF"). discriminate.
  discriminate.
Qed.

Lemma empty_encodes_empty:
  forall l, utf8_encode l = Some "" -> l = [].
Proof.
  destruct l as [|cp l]; unfold utf8_encode; fold utf8_encode.
  + auto.
  + remember (_encode_codepoint cp) as enc_cp.
    destruct (utf8_encode l), enc_cp as [s'|]; try discriminate.
    destruct s'.
    - assert (_encode_codepoint cp <> Some "") as enc_cp_ne by apply encode_codepoint_non_empty.
      rewrite Heqenc_cp in enc_cp_ne; exfalso; apply enc_cp_ne; auto.
    - discriminate.
Qed.

Lemma empty_decodes_empty:
  forall s, utf8_decode s = Some [] -> s = "".
Proof.
  destruct s; unfold utf8_decode.
  + auto.
  + simpl; destruct (_utf8_decode_aux s 0 0 0), a; destruct b2, b3, b4, b5, b6;
    try discriminate; intros Habs; exfalso;
    generalize Habs; apply aux_decode_higher_phase_non_empty.
Qed.

Lemma dec_lemma_1:
  forall cp s s' l,
  0 <= cp <= U+"7F" ->
  utf8_decode s' = Some l ->
  Some (String (ascii_of_N (Z.to_N cp)) "" ++ s') = Some s ->
  utf8_decode s = Some (cp :: l).
Proof.
  intros cp s s' l cp_bounds s'_dec_eq s_eq'; unfold "U+" in *; simpl in *.
  inversion s_eq' as [s_eq]; unfold utf8_decode in *; unfold _utf8_decode_aux; fold _utf8_decode_aux.
  assert (cp = Z.of_N (N_of_ascii (ascii_of_N (Z.to_N cp)))) as cp_eq.
  {
    rewrite N_ascii_embedding by (apply N2Z.inj_lt; rewrite Z2N.id; simpl; omega).
    rewrite Z2N.id; omega.
  }
  rewrite s'_dec_eq.
  destruct (ascii_of_N (Z.to_N cp)); destruct b, b0, b1, b2, b3, b4, b5, b6;
  simpl in *; try omega; rewrite cp_eq; auto.
Qed.

Lemma dec_lemma_2:
  forall cp s s' l,
  U+"7F" < cp <= U+"7FF" ->
  utf8_decode s' = Some l ->
  Some (String (_aux_enc_cp_byte cp 10 6 U+("C0"))
               (String (_aux_enc_cp_byte cp 5 0 U+("80")) "") ++ s') = Some s ->
  utf8_decode s = Some (cp :: l).
Proof.
Admitted. (** FIXME **)

Lemma dec_lemma_3:
  forall cp s s' l,
  (U+"7FF" < cp <= U+"D7FF") \/ (U+"DFFF" < cp <= U+"FFFF") ->
  utf8_decode s' = Some l ->
  Some (String (_aux_enc_cp_byte cp 15 12 U+("E0"))
               (String (_aux_enc_cp_byte cp 11 6 U+("80"))
                       (String (_aux_enc_cp_byte cp 5 0 U+("80")) "")) ++ s') = Some s ->
  utf8_decode s = Some (cp :: l).
Proof.
Admitted. (** FIXME **)

Lemma dec_lemma_4:
  forall cp s s' l,
  U+"FFFF" < cp <= U+"10FFFF" ->
  utf8_decode s' = Some l ->
  Some (String (_aux_enc_cp_byte cp 20 18 U+("F0"))
               (String (_aux_enc_cp_byte cp 17 12 U+("80"))
                       (String (_aux_enc_cp_byte cp 11 6 U+("80"))
                               (String (_aux_enc_cp_byte cp 5 0 U+("80")) ""))) ++ s') = Some s ->
  utf8_decode s = Some (cp :: l).
Proof.
Admitted. (** FIXME **)  

Lemma enc_lemma_1:
  forall a s' cp l,
  Z.of_N (N_of_ascii a) < U+"80" ->
  (forall s'', utf8_encode l = Some s'' <-> _utf8_decode_aux s'' 0 0 0 = Some l) ->
  _utf8_decode_aux (String a s') 0 0 0 = Some (cp :: l) -> 
  utf8_encode (cp :: l) = Some (String a s').
Proof.
  intros a s' cp l a_bounds s'_dec_eq s_dec_eq.
  unfold "U+" in *; simpl in *.
  remember (_utf8_decode_aux s' 0 0 0) as dec_s'.
  destruct a; destruct b, b0, b1, b2, b3, b4, b5, b6;
  simpl in *; try omega;
  destruct dec_s'; try discriminate;
  injection s_dec_eq; intros l_eq cp_eq; rewrite <-cp_eq; simpl;
  assert (utf8_encode l = Some s') as l_enc_eq by (apply s'_dec_eq; rewrite <-l_eq, Heqdec_s'; auto);
  rewrite l_enc_eq; auto.
Qed.

Lemma enc_fail_lemma:
  forall a s',
  (U+"80" <= Z.of_N (N_of_ascii a) < U+"C0") \/ (U+"F8" <= Z.of_N (N_of_ascii a))->
  _utf8_decode_aux (String a s') 0 0 0 = None.
Proof.
  intros a s' a_bounds; unfold "U+" in *; simpl in *.
  destruct a; destruct b, b0, b1, b2, b3, b4, b5, b6;
  simpl in *; auto; omega.
Qed.

Lemma enc_lemma_2:
  forall a s' cp l,
  U+"C0" <= Z.of_N (N_of_ascii a) < U+"E0" ->
  (forall s'', utf8_encode l = Some s'' <-> _utf8_decode_aux s'' 0 0 0 = Some l) ->
  _utf8_decode_aux (String a s') 0 0 0 = Some (cp :: l) -> 
  utf8_encode (cp :: l) = Some (String a s').
Proof.
Admitted. (** FIXME **)

Lemma enc_lemma_3:
  forall a s' cp l,
  U+"E0" <= Z.of_N (N_of_ascii a) < U+"F0" ->
  (forall s'', utf8_encode l = Some s'' <-> _utf8_decode_aux s'' 0 0 0 = Some l) ->
  _utf8_decode_aux (String a s') 0 0 0 = Some (cp :: l) -> 
  utf8_encode (cp :: l) = Some (String a s').
Proof.
Admitted. (** FIXME **)

Lemma enc_lemma_4:
  forall a s' cp l,
  U+"F0" <= Z.of_N (N_of_ascii a) < U+"F8" ->
  (forall s'', utf8_encode l = Some s'' <-> _utf8_decode_aux s'' 0 0 0 = Some l) ->
  _utf8_decode_aux (String a s') 0 0 0 = Some (cp :: l) -> 
  utf8_encode (cp :: l) = Some (String a s').
Proof.
Admitted. (** FIXME **)

Theorem decoded_iff_encoded:
  forall l s, utf8_encode l = Some s <-> utf8_decode s = Some l.
Proof.
  induction l as [|cp l].
  + intros; simpl; split; unfold utf8_decode.
    - intros Heq; injection Heq; intros Heq'; rewrite <-Heq'; auto.
    - destruct s.
      * auto.
      * intros dec_eq; rewrite empty_decodes_empty with (s := String a s); auto.
  + intros; split.
    - unfold utf8_encode; fold utf8_encode.
      destruct (utf8_encode l) as [s'|]; try (destruct (_encode_codepoint cp); discriminate).
      unfold _encode_codepoint.
      destruct (Z_lt_dec cp 0).
        discriminate.
      destruct (Z_le_dec cp U+"7F").
        apply dec_lemma_1; try omega; apply IHl; auto.
      destruct (Z_le_dec cp U+"7FF").
        apply dec_lemma_2; try omega; apply IHl; auto.
      destruct (Z_le_dec cp U+"D7FF").
        apply dec_lemma_3; try omega; apply IHl; auto.
      destruct (Z_le_dec cp U+"DFFF").
        discriminate.
      destruct (Z_le_dec cp U+"FFFF").
        apply dec_lemma_3; try omega; apply IHl; auto.
      destruct (Z_le_dec cp U+"10FFFF").
        apply dec_lemma_4; try omega; apply IHl; auto.
        discriminate.
   - unfold utf8_decode in *.
     destruct s as [|a s'].
       simpl; discriminate.
     destruct (Z_lt_dec (Z.of_N (N_of_ascii a)) U+"80").
       apply enc_lemma_1; auto.
     destruct (Z_lt_dec (Z.of_N (N_of_ascii a)) U+"C0").
       rewrite enc_fail_lemma by omega; discriminate.
     destruct (Z_lt_dec (Z.of_N (N_of_ascii a)) U+"E0").
       apply enc_lemma_2; auto; try omega.
     destruct (Z_lt_dec (Z.of_N (N_of_ascii a)) U+"F0").
       apply enc_lemma_3; auto; try omega.
     destruct (Z_lt_dec (Z.of_N (N_of_ascii a)) U+"F8").
       apply enc_lemma_4; auto; try omega.
       rewrite enc_fail_lemma by omega; discriminate.
Qed.