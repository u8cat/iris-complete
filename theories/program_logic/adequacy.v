(* adequacy.v *)
(* Non-standard variants of adequate. *)

From iris.program_logic Require Export adequacy.

Section steps.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).

  Lemma erased_step_grow t1 σ1 t2 σ2 :
    erased_step (t1,σ1) (t2,σ2) → length t1 ≤ length t2.
  Proof.
    intros [κ Hstep].
    destruct Hstep. simplify_eq.
    rewrite !length_app !length_cons length_app.
    lia.
  Qed.

  Lemma erased_steps_grow t1 σ1 t2 σ2 :
    rtc erased_step (t1,σ1) (t2,σ2) → length t1 ≤ length t2.
  Proof.
    apply (rtc_ind erased_step (λ cfg1 cfg2, length cfg1.1 ≤ length cfg2.1)); clear.
    - intros [t1 σ1]; simpl. reflexivity.
    - intros [t1 σ1] [t2 σ2] [t3 σ3] Hstep _ Hlen. simpl in *.
      etrans; last eassumption.
      by eapply erased_step_grow.
  Qed.

  Lemma erased_step_app t1 σ1 t2 t3 σ2 efs :
    length t1 = length t2 →
    erased_step (t1,σ1) (t2++t3,σ2) →
    erased_step (t1++efs,σ1) (t2++efs++t3,σ2).
  Proof.
    intros Hlen [κ Hstep]. exists κ.
    destruct Hstep as [e1 σ1' e2 σ2' t2' thd ttl Heq1 Heq2 Hprim_step].
    simplify_eq. rename σ1' into σ1. rename σ2' into σ2.
    rename select (t2++t3 = _) into Heq.
    assert (t2 = thd ++ e2 :: ttl ∧ t3 = t2') as [-> <-].
    { apply app_inj_1.
      - rewrite -Hlen !length_app !length_cons //.
      - rewrite Heq app_comm_cons assoc //. }
    apply (step_atomic e1 σ1 e2 σ2 t3 thd (ttl++efs)).
    - rewrite app_comm_cons assoc //.
    - rewrite -!assoc -app_comm_cons //.
    - assumption.
  Qed.

  Lemma erased_steps_app t1 σ1 t2 t3 σ2 efs :
    length t1 = length t2 →
    rtc erased_step (t1,σ1) (t2++t3,σ2) →
    rtc erased_step (t1++efs,σ1) (t2++efs++t3,σ2).
  Proof.
    intros Hlen Hsteps.
    remember (t1,σ1) as cfg1. remember (t2 ++ t3, σ2) as cfg2.
    revert cfg1 cfg2 Hsteps efs t1 σ1 t2 t3 σ2 Heqcfg1 Heqcfg2 Hlen.
    apply (rtc_ind_r_weak (λ cfg1 cfg2, ∀ efs t1 σ1 t2 t3 σ2,
      cfg1 = (t1,σ1) → cfg2 = (t2++t3,σ2) → length t1 = length t2 →
      rtc erased_step (t1++efs,σ1) (t2++efs++t3,σ2))).
    - intros ? efs t1 σ1 t2 t3 σ2 -> Heq Hlen.
      simplify_eq.
      rewrite length_app in Hlen.
      assert (t3=[]) as ->. { apply nil_length_inv. lia. }
      rewrite !right_id //.
    - intros cfg1 [t_mid σ_mid] cfg3 Hsteps Hstep Hind.
      intros efs t1 σ1 t2 t3 σ2 -> -> Hlen.
      pose proof (erased_steps_grow t1 σ1 t_mid σ_mid Hsteps) as Hlen_le.
      rewrite -(take_drop (length t1) t_mid) in Hsteps.
      remember (take (length t1) t_mid) as t_mid1.
      remember (drop (length t1) t_mid) as t_mid2.
      assert (Hlen_t_mid1: length t1 = length t_mid1).
      { rewrite Heqt_mid1 length_take. lia. }
      assert (Heq_tmid: t_mid = t_mid1 ++ t_mid2).
      { rewrite Heqt_mid1 Heqt_mid2 take_drop //. }
      apply (rtc_r _ (t_mid1++efs++t_mid2,σ_mid)).
      + apply Hind; simplify_eq; done.
      + (*      Hstep:
            -------------------
            | t_mid1 | t_mid2 |
            -------------------
                     ↓
            ----------------------
            |  t2    |     t3    |
            ----------------------

                goal:
            ----------=====----------
            | t_mid1 | efs | t_mid2 |
            ----------=====----------
                     ↓
            ----------=====-------------
            |  t2    | efs |     t3    |
            ----------=====------------- *)
        rewrite Hlen_t_mid1 in Hlen.
        destruct Hstep as [κ Hstep].
        exists κ. subst t_mid.
        destruct Hstep as [e1 σ_mid' e2 σ2' efs' thd ttl Heq1 Heq2 Hprim_step].
        simplify_eq. rename σ2' into σ2. rename σ_mid' into σ_mid.
        rename select (t_mid1 ++ t_mid2 = thd ++ e1 :: ttl) into Heq1.
        rename select (t2 ++ t3 = thd ++ e2 :: ttl ++ efs') into Heq2.
        destruct (decide ((length thd) < length t_mid1)) as [Hlen_thd_t_mid1|Hlen_thd_t_mid1].
        * (* Case1:
                      Heq1
            ----------------------------
            |    t_mid1      |  t_mid2 |
            |--------------------------|
            | thd | e1 |     ttl       |
            |--------------------------|
            | thd | e1 |  Δ  |  t_mid2 |
            ---------------------------- *)
          assert (∃ Δ, t_mid1 = thd++e1::Δ ∧ ttl = Δ++t_mid2) as (Δ & -> & ->).
          { exists (drop (S (length thd)) t_mid1). split.
            - apply (f_equal (take (S (length thd)))) in Heq1.
              rewrite (take_app_le t_mid1 t_mid2) in Heq1; last lia.
              replace (thd++e1::ttl) with ((thd++[e1])++ttl) in Heq1 by rewrite -assoc //.
              replace (S (length thd)) with (length (thd++[e1])) in Heq1 by rewrite length_app (comm (Nat.add)) //.
              rewrite take_app_length in Heq1.
              rewrite length_app (comm (Nat.add)) /= in Heq1.
              trans ((thd ++ [e1]) ++ drop (S (length thd)) t_mid1).
              + rewrite -Heq1 take_drop //.
              + rewrite -assoc //.
            - apply (f_equal (drop (S (length thd)))) in Heq1.
              rewrite (drop_app_le t_mid1 t_mid2) in Heq1; last lia.
              rewrite Heq1.
              replace (thd++e1::ttl) with ((thd++[e1])++ttl) by rewrite -assoc //.
              replace (S (length thd)) with (length (thd++[e1])) by rewrite length_app (comm (Nat.add)) //.
              rewrite drop_app_length //. }
          (*            Heq2
            -----------------------------------
            |    t2          |        t3       |
            |----------------------------------|
            | thd | e2 |    ttl       |  efs'  |
            |----------------------------------|
            | thd | e2 |  Δ  | t_mid2 |  efs'  |
            ------------------------------------ *)
          replace (thd ++ e2 :: (Δ ++ t_mid2) ++ efs') with ((thd ++ e2 :: Δ) ++ t_mid2 ++ efs') in Heq2
            by rewrite -!assoc -app_comm_cons //.
          apply app_inj_1 in Heq2 as [-> ->]; last rewrite -Hlen !length_app !length_cons //.

          apply (step_atomic e1 σ_mid e2 σ2 efs' thd (Δ ++ efs++t_mid2));
            [rewrite -!assoc -app_comm_cons //..|done].

        * (* Case2:
                      Heq1
            ----------------------------
            | t_mid1 |    t_mid2       |
            |--------------------------|
            |   thd        | e1 | ttl  |
            |--------------------------|
            | t_mid1 |  Δ  | e1 | ttl  |
            ---------------------------- *)
          assert (∃ Δ, thd = t_mid1++Δ ∧ t_mid2 = Δ++e1::ttl) as (Δ & -> & ->).
          { exists (drop (length t_mid1) thd). split.
            - apply (f_equal (take (length t_mid1))) in Heq1.
              rewrite take_app_length take_app_le in Heq1; last lia.
              rewrite {1}Heq1 take_drop //.
            - apply (f_equal (drop (length t_mid1))) in Heq1.
              rewrite drop_app_length drop_app_le in Heq1; last lia.
              done. }
          (*            Heq2
            ------------------------------------
            |    t2      |          t3         |
            |----------------------------------|
            |     thd        | e2 | ttl | efs' |
            |----------------------------------|
            |   t_mid1   | Δ | e2 | ttl | efs' |
            ------------------------------------ *)
          rewrite -assoc in Heq2.
          apply app_inj_1 in Heq2 as [-> ->]; last rewrite Hlen //.

          apply (step_atomic e1 σ_mid e2 σ2 efs' (t_mid1++efs++Δ) ttl);
            [rewrite -!assoc //..|done].
  Qed.

  Lemma erased_step_cons e1 t1 σ1 e2 t2 σ2 :
    erased_step ([e1],σ1) (e2::t2,σ2) →
    erased_step (e1::t1,σ1) (e2::t1++t2,σ2).
  Proof.
    change (e2::t2) with ([e2]++t2).
    change (e1::t1) with ([e1]++t1).
    change (e2::t1++t2) with ([e2]++t1++t2).
    by apply erased_step_app.
  Qed.

  Lemma erased_steps_cons e1 t1 σ1 e2 t2 σ2 :
    rtc erased_step ([e1],σ1) (e2::t2,σ2) →
    rtc erased_step (e1::t1,σ1) (e2::t1++t2,σ2).
  Proof.
    change (e2::t2) with ([e2]++t2).
    change (e1::t1) with ([e1]++t1).
    change (e2::t1++t2) with ([e2]++t1++t2).
    by apply erased_steps_app.
  Qed.
End steps.

Section adequate_tp.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).

  Record adequate_tp s t1 σ1 (φ : val Λ → state Λ → Prop) := {
    adequate_tp_length : length t1 ≠ 0;
    adequate_tp_result t2 σ2 v2 :
      rtc erased_step (t1, σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
    adequate_tp_not_stuck t2 σ2 e2 :
      s = NotStuck →
      rtc erased_step (t1, σ1) (t2, σ2) →
      e2 ∈ t2 → not_stuck e2 σ2
  }.

  Lemma adequate_tp_adequate s e1 σ1 φ :
    adequate_tp s [e1] σ1 φ ↔ adequate s e1 σ1 φ.
  Proof. by split; intros [??]; split. Qed.

  Lemma adequate_tp_app_l s t1 t2 σ Q :
    t1 ≠ [] → adequate_tp s (t1++t2) σ Q → adequate_tp s t1 σ Q.
  Proof.
    intros Ht1_not_nil [_ Hresult Hnot_stuck].
    split.
    - by destruct t1.
    - intros t3 σ3 v3 Hsteps.
      destruct t1 as [|e1 t1]; first done.
      assert (∃ t3a t3b, t3 = t3a++t3b ∧ length t1 = length t3a) as
        (t3a & t3b & -> & Hlent3a).
      { exists (take (length t1) t3), (drop (length t1) t3).
        split.
        - rewrite take_drop //.
        - pose proof (erased_steps_grow _ _ _ _ Hsteps) as Hlen.
          simpl in Hlen. rewrite length_take. lia. }
      apply (Hresult (t3a++t2++t3b)).
      replace (of_val v3 :: t3a ++ t2 ++ t3b) with ((of_val v3 :: t3a) ++ t2 ++ t3b) by rewrite !app_comm_cons //.
      apply erased_steps_app.
      + rewrite !length_cons. lia.
      + rewrite -!app_comm_cons //.
    - intros t3 σ3 e3 -> Hsteps Hint3.
      assert (∃ t3a t3b, t3 = t3a++t3b ∧ length t1 = length t3a) as
        (t3a & t3b & -> & Hlent3a).
      { exists (take (length t1) t3), (drop (length t1) t3).
        split.
        - rewrite take_drop //.
        - pose proof (erased_steps_grow _ _ _ _ Hsteps) as Hlen.
          simpl in Hlen. rewrite length_take. lia. }
      eapply Hnot_stuck; first reflexivity.
      + eapply erased_steps_app; [exact Hlent3a|exact Hsteps].
      + set_solver.
  Qed.

  Lemma adequate_tp_erased_step t1 σ1 t2 σ2 s Q :
    erased_step (t1,σ1) (t2,σ2) →
    adequate_tp s t1 σ1 Q →
    adequate_tp s t2 σ2 Q.
  Proof.
    intros Hstep [Hlen Hresult Hnot_stuck].
    split.
    - apply erased_step_grow in Hstep. lia.
    - intros t3 σ3 v3 Hsteps.
      eapply Hresult.
      eapply rtc_l; eassumption.
    - intros t3 σ3 e_t3 -> Hsteps.
      eapply Hnot_stuck; first reflexivity.
      eapply rtc_l; first exact Hstep.
      exact Hsteps.
  Qed.
End adequate_tp.

Section adequate.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).
  Lemma adequate_erased_step e1 σ1 e2 σ2 efs s Q :
    erased_step ([e1],σ1) (e2::efs,σ2) →
    adequate s e1 σ1 Q →
    adequate s e2 σ2 Q.
  Proof.
    intros Hstep.
    rewrite -!adequate_tp_adequate.
    intros Hadq.
    eapply adequate_tp_app_l; first done.
    eapply adequate_tp_erased_step; [exact Hstep|exact Hadq].
  Qed.

  Lemma adequate_prim_step e1 σ1 κ e2 σ2 efs s Q :
    prim_step e1 σ1 κ e2 σ2 efs →
    adequate s e1 σ1 Q →
    adequate s e2 σ2 Q.
  Proof.
    intros Hprim_step. eapply adequate_erased_step.
    exists κ.
    by apply (step_atomic e1 σ1 e2 σ2 efs [] []).
  Qed.
End adequate.

Section adequate_nofork.
  Context {Λ : language}.
  Implicit Types (e : expr Λ) (t : list (expr Λ)) (σ : state Λ).
  Implicit Types (κ κs : list (observation Λ)).

  Record adequate_nofork s e1 σ1 (φ : val Λ → state Λ → Prop) := {
    adequate_nofork_nofork t2 σ2 :
      rtc erased_step ([e1], σ1) (t2, σ2) → length t2 = 1;
    adequate_nofork_result t2 σ2 v2 :
      rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
    adequate_nofork_not_stuck t2 σ2 e2 :
      s = NotStuck →
      rtc erased_step ([e1], σ1) (t2, σ2) →
      e2 ∈ t2 → not_stuck e2 σ2
  }.

  Lemma adequate_nofork_erased_step e1 σ1 e2 σ2 s Q :
    erased_step ([e1],σ1) ([e2],σ2) →
    adequate_nofork s e1 σ1 Q →
    adequate_nofork s e2 σ2 Q.
  Proof.
    intros Hstep [Hnofork Hresult Hnot_stuck].
    split.
    - intros t3 σ3 Hsteps.
      eapply Hnofork.
      by eapply rtc_l.
    - intros t3 σ3 v3 Hsteps.
      eapply Hresult.
      by eapply rtc_l.
    - intros t3 σ3 e3 Hs Hsteps.
      eapply Hnot_stuck; first done.
      by eapply rtc_l.
  Qed.

  Lemma adequate_nofork_prim_step e1 σ1 κ e2 σ2 s Q :
    prim_step e1 σ1 κ e2 σ2 [] →
    adequate_nofork s e1 σ1 Q →
    adequate_nofork s e2 σ2 Q.
  Proof.
    intros Hprim_step. eapply adequate_nofork_erased_step.
    exists κ.
    by apply (step_atomic e1 σ1 e2 σ2 [] [] []).
  Qed.
End adequate_nofork.
