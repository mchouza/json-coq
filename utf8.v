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

(** Arithmetical bounds for bitwise ops **)

Lemma pos_lor_lower_bound:
  forall p q, (p <= Pos.lor p q)%positive.
Proof.
  assert (forall p c, Pos.compare_cont p p c = c) as p_p_keeps by
    (induction p; simpl; auto).
  unfold "<="%positive, "?="%positive.
  induction p.
  + simpl; destruct q; simpl; try apply IHp.
    rewrite p_p_keeps; discriminate.
  + simpl; destruct q; simpl; try apply IHp.
    - rewrite Pos.compare_cont_spec.
      specialize IHp with (q := q).
      unfold "?="%positive; destruct Pos.compare_cont; simpl; auto.
      discriminate.
    - rewrite p_p_keeps; discriminate.
  + destruct q; simpl; discriminate.
Qed.

Lemma switch_Eq_Eq:
  forall c, Pos.switch_Eq Eq c = c.
Proof.
  destruct c; simpl; auto.
Qed.

Lemma pos_lor_higher_bound:
  forall p q, (Pos.lor p q <= p + q)%positive.
Proof.
  assert (forall p c, Pos.compare_cont p p c = c) as p_p_keeps by
    (induction p; simpl; auto).
  assert (forall p c, Pos.compare_cont p (Pos.succ p) c = Lt) as p_lt_succ by
    (induction p; simpl; auto).
  unfold "<="%positive, "?="%positive.
  induction p; destruct q; simpl; try apply IHp.
  + specialize IHp with (q := q).
    rewrite Pos.add_carry_spec, Pos.compare_cont_spec in *.
    rewrite switch_Eq_Eq in IHp.
    remember (Pos.lor p q ?= p + q)%positive as lor_sum_cmp.
    destruct lor_sum_cmp; try (rewrite Pos.compare_succ_r, <-Heqlor_sum_cmp; simpl; discriminate).
    exfalso; apply IHp; auto.
  + rewrite p_lt_succ; discriminate.
  + rewrite p_p_keeps; discriminate.
  + rewrite p_lt_succ; discriminate.
  + rewrite p_p_keeps; discriminate.
  + discriminate.
Qed.

Lemma lor_bounds:
  forall a b, 0 <= a -> 0 <= b -> a <= Z.lor a b <= a + b.
Proof.
  intros a b a_ge_0 b_ge_0.
  (* just tries all possible constructors *)
  destruct a, b.
  + auto.
  + simpl; omega.
  + simpl; omega.
  + simpl; omega.
  + (* only nontrivial case *)
    split; [apply pos_lor_lower_bound | apply pos_lor_higher_bound].
  + unfold "<=" in *; simpl in *; auto.
  + unfold "<=" in *; simpl in *; auto.
  + unfold "<=" in *; simpl in *; auto.
  + unfold "<=" in *; simpl in *; auto.
Qed.

Lemma Ndouble_inj_le:
  forall m n, (n <= m -> Pos.Ndouble n <= Pos.Ndouble m)%N.
Proof.
  destruct n, m; simpl; auto.
Qed.

Lemma Nsucc_double_inj_le:
  forall m n, (n <= m -> Pos.Nsucc_double n <= Pos.Nsucc_double m)%N.
Proof.
  destruct n, m; simpl; auto.
Qed.

Lemma pos_land_bound:
  forall p q, (0 <= Pos.land p q <= N.pos p)%N.
Proof.
  assert (forall p, N.pos p~0 = Pos.Ndouble (N.pos p)) as Ndouble_eq by auto.
  assert (forall p, N.pos p~1 = Pos.Nsucc_double (N.pos p)) as Nsucc_double_eq by auto.
  induction p; destruct q; simpl; try (split; discriminate).
  + rewrite Nsucc_double_eq; split.
    - case (Pos.land p q); unfold "<="%N; discriminate.
    - apply Nsucc_double_inj_le, IHp.
  + rewrite Nsucc_double_eq; split.
    - case (Pos.land p q); discriminate.
    - apply N.le_trans with (m := Pos.Ndouble (N.pos p)).
      * apply Ndouble_inj_le, IHp.
      * unfold "<="%N, "?="%N, "?="%positive; simpl.
        rewrite Pos.compare_cont_refl; discriminate.
  + rewrite Ndouble_eq; split.
    - case (Pos.land p q); discriminate.
    - apply Ndouble_inj_le, IHp.
  + rewrite Ndouble_eq; split.
    - case (Pos.land p q); discriminate.
    - apply Ndouble_inj_le, IHp.
Qed.

Lemma land_bounds:
  forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
Proof.
  (* just tries all combinations, previously removing those automatically solved *)
  intros; destruct a, b; auto.
  + (* only nontrivial case *)
    unfold Z.land; rewrite <-N2Z.inj_0, <-N2Z.inj_pos.
    do 2 rewrite <-N2Z.inj_le.
    apply pos_land_bound.
  + unfold "<=" in *; simpl in *; auto.
  + unfold "<=" in *; simpl in *; auto.
  + unfold "<=" in *; simpl in *; auto.
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

(** UTF-8 encoding support **)

Definition _aux_enc_cp_byte cp hi lo offset :=
  ascii_of_N (Z.to_N (Z.lor offset (Z.land (Z.shiftr cp lo) ((Z.shiftl 1 (hi - lo + 1)) - 1)))).

Definition _encode_codepoint cp :=
  match (Z_lt_dec cp 0), (Z_le_dec cp U+"7F"), (Z_le_dec cp U+"7FF"),
        (Z_le_dec cp U+"FFFF"), (Z_le_dec cp U+"10FFFF") with
  | left _, _, _, _, _ => None
  | _, left _, _, _, _ =>
      Some (String (ascii_of_N (Z.to_N cp)) "")
  | _, _, left _, _, _ =>
      Some (String (_aux_enc_cp_byte cp 10 6 U+"C0") 
           (String (_aux_enc_cp_byte cp 5 0 U+"80") ""))
  | _, _, _, left _, _ =>
      Some (String (_aux_enc_cp_byte cp 15 12 U+"E0")
           (String (_aux_enc_cp_byte cp 11 6 U+"80")
           (String (_aux_enc_cp_byte cp 5 0 U+"80") "")))
  | _, _, _, _, left _ =>
      Some (String (_aux_enc_cp_byte cp 20 18 U+"F0")
           (String (_aux_enc_cp_byte cp 17 12 U+"80")
           (String (_aux_enc_cp_byte cp 11 6 U+"80")
           (String (_aux_enc_cp_byte cp 5 0 U+"80") ""))))
  | _, _, _, _, _ => None
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

Inductive is_valid_unicode: list Z -> Prop :=
  | ivu_empty: is_valid_unicode nil
  | ivu_cons: forall c l, 0 <= c <= U+"10FFFF" -> is_valid_unicode l -> is_valid_unicode (c :: l).

Lemma valid_cp_is_encoded:
  forall cp, 0 <= cp <= U+"10FFFF" <-> exists s, _encode_codepoint cp = Some s.
Proof.
  split.
  {
    intros cp_bounds.
    assert (forall s':string, exists s, Some s' = Some s) as ex_eq by (intros; exists s'; auto).
    unfold _encode_codepoint.
    destruct (Z_lt_dec cp 0); try omega.
    destruct (Z_le_dec cp U+"7F"); try apply ex_eq.
    destruct (Z_le_dec cp U+"7FF"); try apply ex_eq.
    destruct (Z_le_dec cp U+"FFFF"); try apply ex_eq.
    destruct (Z_le_dec cp U+"10FFFF"); try apply ex_eq.
    omega.
  }
  {
    intros [s cp_eq].
    unfold _encode_codepoint in cp_eq.
    destruct (Z_lt_dec cp 0); try discriminate cp_eq.
    destruct (Z_le_dec cp U+"7F"); try (unfold "U+" in *; simpl in *; omega).
    destruct (Z_le_dec cp U+"7FF"); try (unfold "U+" in *; simpl in *; omega).
    destruct (Z_le_dec cp U+"FFFF"); try (unfold "U+" in *; simpl in *; omega).
    destruct (Z_le_dec cp U+"10FFFF"); try (unfold "U+" in *; simpl in *; omega).
    discriminate cp_eq.
  }
Qed.

Theorem valid_unicode_is_encoded:
  forall l, is_valid_unicode l <-> exists s, utf8_encode l = Some s.
Proof.
  split.
  {
    intros ivu_l.
    induction ivu_l.
    + exists ""; auto.
    + destruct IHivu_l as [s' l_enc_eq].
      assert (exists s'', _encode_codepoint c = Some s'') as [s'' c_enc_eq]
        by (apply valid_cp_is_encoded; auto).
      simpl; rewrite c_enc_eq, l_enc_eq.
      exists (s'' ++ s'); auto.
  }
  {
    induction l.
    + constructor.
    + intros [s a_l_enc_eq]; constructor.
      - simpl utf8_encode in a_l_enc_eq.
        apply valid_cp_is_encoded.
        destruct (_encode_codepoint a).
        * exists s0; auto.
        * discriminate.
      - apply IHl.
        simpl utf8_encode in a_l_enc_eq.
        destruct (utf8_encode l).
        * exists s0; auto.
        * destruct (_encode_codepoint a); discriminate.
  }
Qed.

Lemma pos_add_carry_bound:
  forall p q, Z.pos (Pos.add p q)~1 < Z.pos (Pos.add_carry p q)~0.
Proof.
  intros.
  rewrite Pos.add_carry_spec, Pos.xI_succ_xO.
  repeat rewrite <-Pos.add_1_r.
  repeat rewrite Pos.add_xO.
  repeat rewrite Pos2Z.inj_add.
  omega.
Qed.

Theorem decode_enc_eq:
  forall l,
  is_valid_unicode l ->
  exists s, utf8_encode l = Some s /\ utf8_decode s = Some l.
Proof.
Admitted. (** FIXME **)
